#include <fstream>
#include <sstream>

#include <llvm/IR/CFG.h>

#include <SVF-FE/LLVMUtil.h>
#include <SVF-FE/PAGBuilder.h>
#include <WPA/Andersen.h>

#include <cbi/target.h>

using namespace SVF;
using namespace llvm;
using namespace std;

#define MAP_SIZE_POW2 18
#define MAP_SIZE (1 << MAP_SIZE_POW2)

using TargetInfos = std::map<BasicBlock *, std::pair<NodeID, cbi::Target>>;

static llvm::cl::opt<std::string> InputFilename(cl::Positional, llvm::cl::desc("<input bitcode>"), llvm::cl::init("-"));

static llvm::cl::opt<std::string> TargetsFile("targets", llvm::cl::desc("specify targes file"), llvm::cl::Required);

SVFModule *svfModule;
ICFG *icfg;
Module *M;
LLVMContext *C;

std::map<const SVFFunction *, double> dTf;
std::map<BasicBlock *, double> dTb;
std::map<BasicBlock *, std::set<BasicBlock *>> criticalBBs;
std::map<BasicBlock *, std::set<BasicBlock *>> solved_bbs;
std::map<Function *, std::set<BasicBlock *>> taint_bbs;

std::map<llvm::BasicBlock *, std::vector<std::string>> condition_infos;
std::map<llvm::BasicBlock *, std::vector<llvm::Value *>> condition_vals;
std::map<llvm::BasicBlock *, uint32_t> condition_ids;
std::map<llvm::BasicBlock *, uint32_t> critical_ids;
uint32_t cond_instrument_num = 0;

GlobalVariable *cvar_map_ptr;
GlobalVariable *cond_map_ptr;

uint32_t numAllBBs = 0;
uint32_t numTargetBBs = 0;
uint32_t numCriticalBBs = 0;

std::map<BasicBlock *, uint32_t> allBBIndices;
std::map<BasicBlock *, uint32_t> targetBBIndices;
std::map<BasicBlock *, uint32_t> criticalBBIndices;

std::map<const SVFFunction *, std::map<BasicBlock *, uint32_t>> targetCGDistances;

std::map<BasicBlock *, std::map<BasicBlock *, uint32_t>> distanceMatrix;

/**
 * Adds the distance between two basic blocks to 'distanceMatrix'.
 *
 * @param from
 * @param to
 * @param distance
 */
void addDistance(BasicBlock *from, BasicBlock *to, uint32_t distance) {
    if (distanceMatrix.count(from) == 0) {
        distanceMatrix.emplace(from, std::map<BasicBlock *, uint32_t>{{to, distance}});
    } else {
        if (distanceMatrix[from].count(to) == 0) {
            distanceMatrix[from].emplace(to, distance);
        } else {
            if (distanceMatrix[from][to] > distance) {
                distanceMatrix[from][to] = distance;
            }
        }
    }
}

/**
 * Sets the indices of regular, critical, and target basic blocks.
 *
 * @param targetInfos
 */
void setBBIndices(const TargetInfos &targetInfos) {
    for (auto &[bb, dist] : dTb) {
        allBBIndices.emplace(bb, numAllBBs++);

        if (targetInfos.count(bb) == 1) {
            targetBBIndices.emplace(bb, numTargetBBs++);
        }

        if (criticalBBs.count(bb) == 1) {
            criticalBBIndices.emplace(bb, numCriticalBBs++);
        }
    }
}

/**
 * Writes the values of a matrix into a file.
 *
 * @param filepath
 * @param matrix
 * @param nRows
 * @param nColumns
 * @param writeDims
 * @param delimiter
 */
void writeMatrix(const std::string &filepath,
                 const std::vector<std::vector<int32_t>> &matrix,
                 uint32_t nRows,
                 uint32_t nColumns,
                 bool writeDims = true,
                 char delimiter = ',') {
    std::ofstream outputFile(filepath);

    if (!outputFile.is_open()) {
        std::cout << "Failed to open the output file." << std::endl;
        return;
    }

    if (writeDims) {
        // Write the matrix dimensions to the file
        outputFile << nRows << ":" << nColumns << std::endl;
    }

    // Write the matrix values to the file
    for (int i = 0; i < nRows; i++) {
        for (int j = 0; j < nColumns; j++) {
            outputFile << matrix[i][j];

            if (j < (numTargetBBs - 1)) {
                outputFile << delimiter;
            }
        }
        outputFile << std::endl;
    }

    outputFile.close();
}

/**
 * Writes the distance values from critical to all target basic blocks into a file.
 *
 * @param filepath
 */
void writeDistanceMatrix(const std::string &filepath) {
    std::vector<std::vector<int32_t>> matrixArray(numCriticalBBs, std::vector<int32_t>(numTargetBBs));

    for (auto &[criticalBB, criticalBBId] : criticalBBIndices) {
        assert(!distanceMatrix.at(criticalBB).empty());

#ifdef CBI_DEBUG
        cout << criticalBBId << " (" << distanceMatrix[criticalBB].size() << "): ";
        for (auto &[targetBB, targetDist] : distanceMatrix[criticalBB]) {
            cout << targetDist << " ";
        }
        cout << endl;
#endif

        for (auto &[targetBB, targetBBId] : targetBBIndices) {
            if (distanceMatrix.at(criticalBB).count(targetBB) == 0) {
                // The target BB is unreachable from the current critical BB
                matrixArray[criticalBBId][targetBBId] = -1;
            } else {
                matrixArray[criticalBBId][targetBBId] = distanceMatrix[criticalBB][targetBB];
            }
        }
    }

    writeMatrix(filepath, matrixArray, numCriticalBBs, numTargetBBs);
}

/**
 * Retrieves the debug information (source location) associated with a given basic block.
 *
 * @param bb The basic block to retrieve the debug information from.
 * @return The debug information (source location) as a string.
 */
std::string getDebugInfo(BasicBlock *bb) {
    for (auto &it : *bb) {
        std::string str = SVFUtil::getSourceLoc(&it);
        if (str != "{  }" && str.find("ln: 0  cl: 0") == std::string::npos) {
            return str;
        }
    }
    return "{ }";
}

/**
 * Checks if there is a control-flow edge forming a loop between two basic blocks.
 *
 * @param loop_info Pointer to the LoopInfoBase object.
 * @param src The source basic block.
 * @param dst The destination basic block.
 * @return True if there is a loop edge, false otherwise.
 */
bool isCircleEdge(llvm::LoopInfoBase<llvm::BasicBlock, llvm::Loop> *loop_info, BasicBlock *src, BasicBlock *dst) {
    if (loop_info->getLoopFor(src) == loop_info->getLoopFor(dst)) {
        if (!(loop_info->isLoopHeader(src)) && loop_info->isLoopHeader(dst)) {
            return true;
        }
    }
    return false;
}

/**
 * Counts the control-flow graph distance between the specified target nodes and their respective functions.
 *
 * @param targetInfos
 */
void countCGDistance(const TargetInfos &targetInfos) {
    FIFOWorkList<const FunEntryBlockNode *> worklist;
    std::map<BasicBlock *, std::map<const SVFFunction *, uint32_t>> dtf;

    // Calculate the function distance to each target.
    for (const auto &[bb, targetPair] : targetInfos) {
        NodeID targetId = targetPair.first;
        std::set<const FunEntryBlockNode *> visited;

        ICFGNode *iNode = icfg->getICFGNode(targetId);
        FunEntryBlockNode *fNode = icfg->getFunEntryBlockNode(iNode->getFun());
        worklist.push(fNode);

        std::map<const SVFFunction *, uint32_t> df;
        df[iNode->getFun()] = 1;

        targetCGDistances[iNode->getFun()][bb] = 1;

        while (!worklist.empty()) {
            const FunEntryBlockNode *vNode = worklist.pop();

            for (auto it = vNode->InEdgeBegin(), eit = vNode->InEdgeEnd(); it != eit; ++it) {
                ICFGEdge *edge = *it;
                ICFGNode *srcNode = edge->getSrcNode();
                const SVFFunction *svffunc = srcNode->getFun();
                FunEntryBlockNode *vfNode = icfg->getFunEntryBlockNode(svffunc);

                if ((df.count(svffunc) == 0) || (df[svffunc] > (df[vNode->getFun()] + 1))) {
                    df[svffunc] = df[vNode->getFun()] + 1;
                    worklist.push(vfNode);
                }
            }
        }
        dtf[bb] = df;
    }

    for (auto svffun : *svfModule) {
        double df_tmp = 0;
        bool flag = false;

        for (auto &[bb, df] : dtf) {
            if (df.count(svffun) != 0) {
                if (df[svffun] != 0) {
                    df_tmp += (double)1 / df[svffun];

                    targetCGDistances[svffun][bb] = 10 * df[svffun];
                }
                flag = true;
            }
        }

        if (flag) {
            if (df_tmp != 0) {
                dTf[svffun] = (double)1 / df_tmp;
            } else {
                dTf[svffun] = 0;
            }
        }
    }
}

/**
 * Counts the control-flow graph distance between basic blocks within a function.
 *
 * @param svffun A SVFFunction pointer representing the function.
 */
void countCFGDistance(const SVFFunction *svffun, const TargetInfos &targetInfos) {
    std::map<BasicBlock *, std::map<BasicBlock *, uint32_t>> dtb;
    std::set<BasicBlock *> target_bbs;

    std::map<BasicBlock *, const SVFFunction *> functionCalls;

    for (auto &bit : *svffun->getLLVMFun()) {
        BasicBlock *bb = &bit;
        for (BasicBlock::iterator it = bb->begin(), eit = bb->end(); it != eit; ++it) {
            Instruction *inst = &(*it);
            if (auto *CB = dyn_cast<CallBase>(inst)) {
                if (!CB->getCalledFunction()) {
                    continue;
                }

                const SVFFunction *svffunc_tmp = svfModule->getSVFFunction(CB->getCalledFunction());

                if (dTf.count(svffunc_tmp) != 0) {
                    functionCalls.emplace(bb, svffunc_tmp);

                    if (target_bbs.find(bb) != target_bbs.end()) {
                        if (dTb[bb] > 10 * dTf[svffunc_tmp]) {
                            dTb[bb] = 10 * dTf[svffunc_tmp];
                            functionCalls[bb] = svffunc_tmp;
                        }
                    } else {
                        target_bbs.insert(bb);
                        dTb[bb] = 10 * dTf[svffunc_tmp];
                        functionCalls[bb] = svffunc_tmp;
                    }
                }
            }
        }

        if (targetInfos.count(bb)) {
            dTb[bb] = 0;
            target_bbs.insert(bb);
        }
    }

    // func_targets[svffun->getLLVMFun()] = target_bbs;

    std::set<BasicBlock *> tmp_taint_bbs;

    llvm::DominatorTree DT = llvm::DominatorTree();
    llvm::PostDominatorTree PDT = llvm::PostDominatorTree();
    auto *LoopInfo = new llvm::LoopInfoBase<llvm::BasicBlock, llvm::Loop>();

    if (!(svffun->getLLVMFun()->isDeclaration())) {
        DT.recalculate(*(svffun->getLLVMFun()));
        PDT.recalculate(*(svffun->getLLVMFun()));
        LoopInfo->releaseMemory();
        LoopInfo->analyze(DT);
    }

    for (BasicBlock *bb : target_bbs) {
        FIFOWorkList<BasicBlock *> worklist;
        std::set<BasicBlock *> visited;

        worklist.push(bb);

        while (!worklist.empty()) {
            BasicBlock *vbb = worklist.pop();
            tmp_taint_bbs.insert(vbb);

            for (BasicBlock *srcbb : predecessors(vbb)) {
                if (visited.find(srcbb) == visited.end() && !isCircleEdge(LoopInfo, srcbb, vbb)) {
                    worklist.push(srcbb);
                    visited.insert(srcbb);
                }
            }
        }
    }

    taint_bbs[svffun->getLLVMFun()] = tmp_taint_bbs;

    for (BasicBlock *bb : target_bbs) {
        std::map<BasicBlock *, uint32_t> db;
        db[bb] = 0;

        FIFOWorkList<BasicBlock *> worklist;
        std::set<BasicBlock *> visited;

        worklist.push(bb);

        while (!worklist.empty()) {
            BasicBlock *vbb = worklist.pop();
            for (BasicBlock *srcbb : predecessors(vbb)) {
                if ((db.count(srcbb) == 0) || (db[srcbb] > (db[vbb] + 1))) {
                    db[srcbb] = db[vbb] + 1;
                    worklist.push(srcbb);
                }
            }
        }

        dtb[bb] = db;
    }

    for (auto &bit : *svffun->getLLVMFun()) {
        BasicBlock *bb = &bit;

        if (target_bbs.find(bb) != target_bbs.end()) {
            if (functionCalls.count(bb) == 0) {
                // Target BB (trivial case)
                addDistance(bb, bb, 0);
            } else {
                // Target function call BB
                for (auto &[targetBB, targetDist] : targetCGDistances.at(functionCalls[bb])) {
                    addDistance(bb, targetBB, targetDist);
                }
            }
            continue;
        }

        double db_tmp = 0;
        bool flag = false;
        for (auto db : dtb) {
            if (db.second.count(bb)) {
                db_tmp += (double)1 / (db.second[bb] + dTb[db.first]);
                flag = true;

                if (functionCalls.count(bb) == 0 || targetInfos.count(bb)) {
                    // Target BB
                    addDistance(bb, db.first, db.second[bb]);
                } else {
                    // Target function call BB
                    for (auto &[targetBB, targetDist] : targetCGDistances.at(functionCalls[db.first])) {
                        addDistance(bb, targetBB, db.second[bb] + targetDist);
                    }
                }
            }
        }

        if (flag) {
            dTb[bb] = (double)1 / db_tmp;
        }
    }
}

/**
 * Counts the vanilla distance (control-flow graph and call graph distance) between targets.
 *
 * @param targetInfos
 */
void countVanillaDistance(const TargetInfos &targetInfos) {
    countCGDistance(targetInfos);

    for (auto svffun : *svfModule) {
        countCFGDistance(svffun, targetInfos);
    }
}

/**
 * Identifies the critical basic blocks in the program based on control-flow and taint analysis.
 */
void identifyCriticalBB() {
    for (auto svffun : *svfModule) {
        for (Function::iterator bit = svffun->getLLVMFun()->begin(), ebit = svffun->getLLVMFun()->end(); bit != ebit;
             ++bit) {
            BasicBlock *bb = &*(bit);
            std::set<BasicBlock *> tmp_critical_bbs;
            std::set<BasicBlock *> tmp_solved_bbs;
            if (!bb->getSingleSuccessor() && taint_bbs.count(svffun->getLLVMFun()) &&
                taint_bbs[svffun->getLLVMFun()].count(bb)) {
                for (BasicBlock *dstbb : successors(bb)) {
                    if (taint_bbs[svffun->getLLVMFun()].count(dstbb) == 0) {
                        tmp_critical_bbs.insert(dstbb);
                    } else {
                        tmp_solved_bbs.insert(dstbb);
                    }
                }
            }
            if (!tmp_critical_bbs.empty()) {
                criticalBBs[bb] = tmp_critical_bbs;
                solved_bbs[bb] = tmp_solved_bbs;
            }
        }
    }

    int temp_count = 0;
    int temp_count2 = 0;
    int temp_count3 = 0;
    for (const auto &item : criticalBBs) {
        llvm::BasicBlock *bb = item.first;
        llvm::Instruction &inst = bb->back();
        if (auto *br = dyn_cast<BranchInst>(&inst)) {
            Value *br_v = br->getOperand(0);
            temp_count2++;
            if (auto *cmp = dyn_cast<CmpInst>(br_v)) {
                temp_count++;
            }
        } else if (dyn_cast<SwitchInst>(&inst)) {
            temp_count3++;
        }
    }
}

/**
 * Instruments the program by adding the necessary code to collect distance information.
 *
 * @param targetInfos
 */
void instrument(const TargetInfos &targetInfos) {
    ofstream distanceFile("distance.txt", std::ios::out);
    ofstream functionFile("functions.txt", std::ios::out);
    ofstream targetBBFile("targets.txt", std::ios::out);

    uint32_t func_id = 0;

    uint32_t v_instrument_num = 0;
    uint32_t c_instrument_num = 0;

    IntegerType *Int8Ty = IntegerType::getInt8Ty(*C);
    IntegerType *Int32Ty = IntegerType::getInt32Ty(*C);
    IntegerType *Int64Ty = IntegerType::getInt64Ty(*C);

    GlobalVariable *AFLMapPtr = (GlobalVariable *)M->getOrInsertGlobal(
            "__afl_area_ptr", PointerType::get(IntegerType::getInt8Ty(*C), 0), []() -> GlobalVariable * {
                return new GlobalVariable(*M, PointerType::get(IntegerType::getInt8Ty(M->getContext()), 0), false,
                                          GlobalValue::ExternalLinkage, nullptr, "__afl_area_ptr");
            });

    GlobalVariable *CBMapPtr = (GlobalVariable *)M->getOrInsertGlobal(
            "__critical_bb_ptr", PointerType::get(IntegerType::getInt8Ty(*C), 0), []() -> GlobalVariable * {
                return new GlobalVariable(*M, PointerType::get(IntegerType::getInt8Ty(M->getContext()), 0), false,
                                          GlobalValue::ExternalLinkage, nullptr, "__critical_bb_ptr");
            });

    GlobalVariable *DBMapPtr = (GlobalVariable *)M->getOrInsertGlobal(
            "__distance_bb_ptr", PointerType::get(IntegerType::getInt8Ty(*C), 0), []() -> GlobalVariable * {
                return new GlobalVariable(*M, PointerType::get(IntegerType::getInt8Ty(M->getContext()), 0), false,
                                          GlobalValue::ExternalLinkage, nullptr, "__distance_bb_ptr");
            });

    IntegerType *LargestType = Int64Ty;
    ConstantInt *MapCntLoc = ConstantInt::get(LargestType, MAP_SIZE + 8);

    ConstantInt *MapDistLoc = ConstantInt::get(LargestType, MAP_SIZE);
    ConstantInt *One = ConstantInt::get(LargestType, 1);

    distanceFile << numCriticalBBs << std::endl;
    targetBBFile << numTargetBBs << std::endl;

    for (auto svffun : *svfModule) {
        bool flag = false;
        for (auto &bit : *svffun->getLLVMFun()) {
            BasicBlock *bb = &bit;
            if (dTb.count(bb)) {
                uint32_t bbId = allBBIndices.at(bb);

                /* Ensure distance is not zero for non-target basic blocks */
                double rawDistance = 100.0 * dTb[bb];
                uint32_t distance;
                if (rawDistance < 1.0 && rawDistance > 0.0) {
                    distance = 1;
                } else {
                    distance = (uint32_t)(rawDistance);
                }

                ConstantInt *Distance = ConstantInt::get(LargestType, (unsigned)distance);

                BasicBlock::iterator IP = bb->getFirstInsertionPt();
                llvm::IRBuilder<> IRB(&(*IP));

                /* Load SHM pointer */

                LoadInst *MapPtr = IRB.CreateLoad(AFLMapPtr);
                MapPtr->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));

                /* Add distance to shm[MAPSIZE] */

                Value *MapDistPtr = IRB.CreateBitCast(IRB.CreateGEP(MapPtr, MapDistLoc), LargestType->getPointerTo());
                LoadInst *MapDist = IRB.CreateLoad(MapDistPtr);
                MapDist->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));

                Value *IncrDist = IRB.CreateAdd(MapDist, Distance);
                IRB.CreateStore(IncrDist, MapDistPtr)->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));

                /* Increase count at shm[MAPSIZE + (4 or 8)] */

                Value *MapCntPtr = IRB.CreateBitCast(IRB.CreateGEP(MapPtr, MapCntLoc), LargestType->getPointerTo());
                LoadInst *MapCnt = IRB.CreateLoad(MapCntPtr);
                MapCnt->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));

                Value *IncrCnt = IRB.CreateAdd(MapCnt, One);
                IRB.CreateStore(IncrCnt, MapCntPtr)->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));

                if (distance == 0) {
                    // Target BBs ...
                    uint32_t targetBBId = targetBBIndices.at(bb);

                    ConstantInt *TFlagLoc = ConstantInt::get(LargestType, MAP_SIZE + 16 + targetBBId);
                    Value *TFlagPtr = IRB.CreateGEP(MapPtr, TFlagLoc);
                    ConstantInt *FlagOne = ConstantInt::get(Int8Ty, 1);

                    IRB.CreateStore(FlagOne, TFlagPtr)
                            ->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));

                    double bbScore;

                    auto mapPos = targetInfos.find(bb);
                    if (mapPos == targetInfos.end()) {
                        // Hm something went wrong! Normally, all target BBs should be contained in 'targetInfos'.
                        bbScore = 0.0;
                    } else {
                        cbi::Target target = mapPos->second.second;
                        bbScore = target.getScore();
                    }

                    targetBBFile << targetBBId << " " << bbScore << " " << getDebugInfo(bb) << std::endl;
                }

                if (criticalBBs.count(bb)) {
                    for (auto cbb : criticalBBs[bb]) {
                        BasicBlock::iterator IP2 = cbb->getFirstInsertionPt();
                        llvm::IRBuilder<> IRB2(&(*IP2));

                        LoadInst *CBPtr = IRB2.CreateLoad(CBMapPtr);
                        CBPtr->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));

                        ConstantInt *CBIdx = ConstantInt::get(Int32Ty, bbId);
                        ConstantInt *CBOne = ConstantInt::get(Int8Ty, 1);
                        Value *CBIdxPtr = IRB2.CreateGEP(CBPtr, CBIdx);
                        IRB2.CreateStore(CBOne, CBIdxPtr)
                                ->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));

                        c_instrument_num++;
                    }

                    critical_ids[bb] = bbId;
                }

                if (solved_bbs.count(bb)) {
                    for (auto sbb : solved_bbs[bb]) {
                        BasicBlock::iterator IP2 = sbb->getFirstInsertionPt();
                        llvm::IRBuilder<> IRB2(&(*IP2));

                        LoadInst *CBPtr = IRB2.CreateLoad(CBMapPtr);
                        CBPtr->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));

                        ConstantInt *CBIdx = ConstantInt::get(Int32Ty, bbId);
                        ConstantInt *CBOne = ConstantInt::get(Int8Ty, 2);
                        Value *CBIdxPtr = IRB2.CreateGEP(CBPtr, CBIdx);
                        IRB2.CreateStore(CBOne, CBIdxPtr)
                                ->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));
                    }
                }

                distanceFile << bbId << " ";
                if (criticalBBs.count(bb)) {
                    distanceFile << criticalBBIndices.at(bb) << " ";
                } else {
                    distanceFile << "-1 ";
                }
                distanceFile << distance << " " << getDebugInfo(bb) << std::endl;

                flag = true;
                v_instrument_num++;
            }
        }

        if (flag) {
            functionFile << func_id << " " << SVFUtil::getSourceLocOfFunction(svffun->getLLVMFun()) << std::endl;
            func_id++;
        }
    }

    distanceFile.close();
    functionFile.close();
    targetBBFile.close();
}

/**
 * Analyzes the if-conditions in the given SVF module.
 */
void analyzeCondition() {
    u32_t condition_id = 1;

    for (auto svffun : *svfModule) {
        for (auto &bit : *svffun->getLLVMFun()) {
            BasicBlock *bb = &bit;
            if (bb->getSingleSuccessor()) {
                continue;
            }
            llvm::Instruction &inst = bb->back();
            if (auto *br = dyn_cast<BranchInst>(&inst)) {
                Value *br_v = br->getOperand(0);
                if (auto *cmp = dyn_cast<CmpInst>(br_v)) {
                    std::vector<std::string> condition_info;
                    std::vector<llvm::Value *> condition_val;
                    Value *op1 = cmp->getOperand(0);
                    Value *op2 = cmp->getOperand(1);
                    std::string op1_ty = "none";
                    std::string op2_ty = "none";
                    std::string op1_val = "none";
                    std::string op2_val = "none";
                    bool need_record = false;

                    if (op1->getType()->isIntegerTy()) {
                        auto *int_ty = dyn_cast<IntegerType>(op1->getType());
                        op1_ty = "";
                        op1_ty += "int";
                        op1_ty += std::to_string(int_ty->getBitWidth());
                        if (int_ty->getBitWidth() >= 32) {
                            need_record = true;
                        }
                    }

                    if (op2->getType()->isIntegerTy()) {
                        auto *int_ty2 = dyn_cast<IntegerType>(op1->getType());
                        op2_ty = "";
                        op2_ty += "int";
                        op2_ty += std::to_string(int_ty2->getBitWidth());
                    }

                    if (!llvm::Constant::classof(op1)) {
                        op1_val = "var";
                    } else {
                        if (auto *constantint = llvm::dyn_cast<llvm::ConstantInt>(op1)) {
                            op1_val = std::to_string(constantint->getSExtValue());
                        }
                    }

                    if (!llvm::Constant::classof(op2)) {
                        op2_val = "var";
                    } else {
                        if (auto *constantint = llvm::dyn_cast<llvm::ConstantInt>(op2)) {
                            op2_val = std::to_string(constantint->getSExtValue());
                        }
                    }

                    if (auto *CB = dyn_cast<CallBase>(op1)) {
                        if (CB->getCalledFunction()) {
                            if (CB->getCalledFunction()->getName().str() == "strcmp") {
                                Value *arg1 = CB->getArgOperand(0);
                                Value *arg2 = CB->getArgOperand(1);
                                if (auto *get_element = dyn_cast<GetElementPtrInst>(arg2)) {
                                    if (auto *str_global = dyn_cast<GlobalVariable>(get_element->getPointerOperand())) {
                                        if (auto *str_val = dyn_cast<ConstantDataArray>(str_global->getInitializer())) {
                                            op1_ty = "str";
                                            op1_val = "var";
                                            op2_ty = "str_const";
                                            if (str_val->isString()) {
                                                op2_val = str_val->getAsString().str();
                                                op1 = arg1;
                                                op2 = arg2;
                                                if (op2_val.length() <= 8) {
                                                    need_record = true;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }

                    if (need_record) {
                        condition_val.push_back(op1);
                        condition_val.push_back(op2);
                        condition_info.push_back(op1_ty);
                        condition_info.push_back(op2_ty);
                        condition_info.push_back(op1_val);
                        condition_info.push_back(op2_val);
                        condition_infos[bb] = condition_info;
                        condition_vals[bb] = condition_val;
                        condition_ids[bb] = condition_id;
                        condition_id++;
                    }
                }
            }
        }
    }
    ofstream outfile;
    outfile.open("condition_info.txt", std::ios::out);

    if (!outfile.is_open()) {
        std::cerr << "EError opening file" << std::endl;
        exit(1);
    }

    for (auto info : condition_infos) {
        if (criticalBBs.count(info.first)) {
            outfile << condition_ids[info.first] << " " << critical_ids[info.first] << " " << info.second[0] << " "
                    << info.second[1] << " " << info.second[2] << " " << info.second[3] << " " << std::endl;
        } else {
            outfile << condition_ids[info.first] << " none " << info.second[0] << " " << info.second[1] << " "
                    << info.second[2] << " " << info.second[3] << " " << std::endl;
        }
    }

    outfile.close();
}

/**
 * Instruments the basic block with the given variable and index.
 *
 * @param bb The basic block to instrument.
 * @param var The variable to instrument.
 * @param idx The index of the instrumented condition.
 */
void instrumentBB(llvm::BasicBlock *bb, llvm::Value *var, uint8_t idx) {
    auto *term_inst = dyn_cast<Instruction>(bb->getTerminator());
    if (term_inst == nullptr) {
        return;
    }

    llvm::IRBuilder<> IRB(term_inst);
    auto *branch = dyn_cast<BranchInst>(term_inst);
    Value *branch_val = IRB.CreateZExt(branch->getCondition(), IRB.getInt8Ty());

    llvm::LoadInst *c_map_ptr = IRB.CreateLoad(cond_map_ptr);
    llvm::Value *cond_map_ptr_idx =
            IRB.CreateGEP(c_map_ptr, ConstantInt::get(IntegerType::getInt32Ty(*C), condition_ids[bb]));
    branch_val = IRB.CreateAdd(branch_val, ConstantInt::get(IntegerType::getInt8Ty(*C), 1));
    IRB.CreateStore(branch_val, cond_map_ptr_idx);

    llvm::LoadInst *map_ptr = IRB.CreateLoad(cvar_map_ptr);
    ConstantInt *cur_id = llvm::ConstantInt::get(IntegerType::getInt32Ty(*C), 2 * condition_ids[bb] + idx);
    llvm::Value *map_ptr_idx = IRB.CreateGEP(map_ptr, cur_id);
    Value *var_64 = IRB.CreateIntCast(var, IntegerType::getInt64Ty(*C), true);
    IRB.CreateStore(var_64, map_ptr_idx);

    cond_instrument_num++;
}

/**
 * Instruments the basic block with the given string variable.
 *
 * @param bb The basic block to instrument.
 * @param var The string variable to instrument.
 */
void instrumentString(llvm::BasicBlock *bb, llvm::Value *var) {
    auto *term_inst = dyn_cast<Instruction>(bb->getTerminator());
    if (term_inst == nullptr) {
        return;
    }

    llvm::IRBuilder<> IRB(term_inst);
    auto *branch = dyn_cast<BranchInst>(term_inst);
    Value *branch_val = IRB.CreateZExt(branch->getCondition(), IRB.getInt8Ty());

    llvm::LoadInst *c_map_ptr = IRB.CreateLoad(cond_map_ptr);
    llvm::Value *cond_map_ptr_idx =
            IRB.CreateGEP(c_map_ptr, ConstantInt::get(IntegerType::getInt32Ty(*C), condition_ids[bb]));
    branch_val = IRB.CreateAdd(branch_val, ConstantInt::get(IntegerType::getInt8Ty(*C), 1));
    IRB.CreateStore(branch_val, cond_map_ptr_idx);

    llvm::LoadInst *map_ptr = IRB.CreateLoad(cvar_map_ptr);
    ConstantInt *cur_id = llvm::ConstantInt::get(IntegerType::getInt32Ty(*C), 2 * condition_ids[bb]);
    llvm::Value *map_ptr_idx = IRB.CreateGEP(map_ptr, cur_id);
    llvm::Value *ptr_64 = IRB.CreatePointerCast(var, PointerType::get(IntegerType::getInt64Ty(*C), 0));
    llvm::Value *var_64 = IRB.CreateLoad(ptr_64);
    IRB.CreateStore(var_64, map_ptr_idx);

    cond_instrument_num++;
}

/**
 * Instruments the conditions based on the analyzed information.
 */
void instrumentCondition() {
    IntegerType *Int64Ty = IntegerType::getInt64Ty(*C);
    IntegerType *Int8Ty = IntegerType::getInt8Ty(*C);
    cvar_map_ptr =
            new GlobalVariable(*(LLVMModuleSet::getLLVMModuleSet()->getMainLLVMModule()), PointerType::get(Int64Ty, 0),
                               false, GlobalValue::ExternalLinkage, 0, "__cvar_map_ptr");
    cond_map_ptr =
            new GlobalVariable(*(LLVMModuleSet::getLLVMModuleSet()->getMainLLVMModule()), PointerType::get(Int8Ty, 0),
                               false, GlobalValue::ExternalLinkage, 0, "__cond_map_ptr");

    for (auto info : condition_infos) {
        if ((info.second[0].find("int") != std::string::npos) && (info.second[2] == "var")) {
            instrumentBB(info.first, condition_vals[info.first][0], 0);  // Left operand
        }

        if ((info.second[1].find("int") != std::string::npos) && (info.second[3] == "var")) {
            instrumentBB(info.first, condition_vals[info.first][1], 1);  // Right operand
        }

        if (info.second[1] == "str_const") {
            instrumentString(info.first, condition_vals[info.first][0]);
        }
    }
}

/**
 * Loads target information from the given CSV file.
 *
 * @param filename
 * @return
 */
TargetInfos loadTargets(const std::string &filename) {
    ifstream inFile(filename);
    if (!inFile) {
        std::cerr << "Can't open target file!" << std::endl;
        exit(1);
    }

    TargetInfos targetInfos;
    std::vector<cbi::Target> targets;

    std::string csvLine;
    while (getline(inFile, csvLine)) {
        targets.emplace_back(cbi::Target::fromLine(csvLine));
    }

    // Iterate over all basic blocks and located the target NodeIDs
    for (auto fun : *svfModule) {
        Function *F = fun->getLLVMFun();
        std::string file_name;

        if (llvm::DISubprogram *SP = F->getSubprogram()) {
            if (SP->describes(F)) {
                file_name = (SP->getFilename()).str();
            }
        }

        bool flag = false;
        for (const auto &target : targets) {
            auto idx = file_name.find(target.getFilename());
            if (idx != string::npos) {
                flag = true;
                break;
            }
        }

        if (!flag) {
            continue;
        }

        for (auto &bit : *fun->getLLVMFun()) {
            BasicBlock *bb = &bit;
            std::string tmp_string = getDebugInfo(bb);
            for (auto &it : *bb) {
                uint32_t line_num = 0;
                Instruction *inst = &it;
                std::string str = SVFUtil::getSourceLoc(inst);

                if (SVFUtil::isa<AllocaInst>(inst)) {
                    for (llvm::DbgInfoIntrinsic *DII : FindDbgAddrUses(const_cast<Instruction *>(inst))) {
                        if (auto *DDI = SVFUtil::dyn_cast<llvm::DbgDeclareInst>(DII)) {
                            auto *DIVar = SVFUtil::cast<llvm::DIVariable>(DDI->getVariable());
                            line_num = DIVar->getLine();
                        }
                    }
                } else if (MDNode *N = inst->getMetadata("dbg")) {
                    auto *Loc = SVFUtil::cast<llvm::DILocation>(N);
                    line_num = Loc->getLine();
                }

                // If the line number matches that in targets then add to the result set
                for (const auto &target : targets) {
                    auto idx = file_name.find(target.getFilename());
                    if (idx != string::npos && (idx == 0 || file_name[idx - 1] == '/')) {
                        if (target.getLineNumber() == line_num) {
                            NodeID nodeId = icfg->getBlockICFGNode(inst)->getId();
                            targetInfos.insert({bb, {nodeId, target}});
                        }
                    }
                }
            }
        }
    }
    inFile.close();

    return targetInfos;
}

int main(int argc, char **argv) {
    int arg_num = 0;
    char **arg_value = new char *[argc];
    std::vector<std::string> moduleNameVec;
    SVFUtil::processArguments(argc, argv, arg_num, arg_value, moduleNameVec);
    cl::ParseCommandLineOptions(arg_num, arg_value, "Analyze the target BB distances\n");

    svfModule = LLVMModuleSet::getLLVMModuleSet()->buildSVFModule(moduleNameVec);

    icfg = new ICFG();
    ICFGBuilder builder(icfg);
    builder.build(svfModule);

    M = LLVMModuleSet::getLLVMModuleSet()->getMainLLVMModule();
    C = &(LLVMModuleSet::getLLVMModuleSet()->getContext());

    auto targetInfos = loadTargets(TargetsFile);

    countVanillaDistance(targetInfos);
    identifyCriticalBB();

    setBBIndices(targetInfos);
    assert(targetBBIndices.size() == targetInfos.size());
    assert(criticalBBIndices.size() == criticalBBs.size());

    instrument(targetInfos);
    analyzeCondition();
    instrumentCondition();

    writeDistanceMatrix("dm.csv");

    LLVMModuleSet::getLLVMModuleSet()->dumpModulesToFile(".ci.bc");

    delete icfg;

    return 0;
}