/**
 * Copyright 2023-2024 XXX
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <SVF-FE/LLVMUtil.h>
#include <WPA/Andersen.h>

#include <sfi/inspector.h>
#include <sfi/llvm_utils.h>

using namespace std;
using namespace sfi;

/**
 * Macro to get the main LLVM module from a given set of modules.
 *
 * @param moduleSet A pointer to the set of modules.
 * @return The main LLVM module of the given module set.
 */
#define LLVM_MODULE(moduleSet) ((moduleSet)->getMainLLVMModule())

/**
 * Macro to get the DWARF version of the main LLVM module in a given set of modules.
 *
 * @param moduleSet A pointer to the set of modules.
 * @return The DWARF version of the main LLVM module of the given module set.
 */
#define LLVM_DWARF_VERSION(moduleSet) (LLVM_MODULE(moduleSet)->getDwarfVersion())

Inspector::Inspector(string bitcodeFile) noexcept(false) {
    SVF::SVFModule *svfModule = SVF::LLVMModuleSet::getLLVMModuleSet()->buildSVFModule({bitcodeFile});

    // Check if the DWARF version of the LLVM module is 0, which means there is missing debug information
    if (LLVM_DWARF_VERSION(SVF::LLVMModuleSet::getLLVMModuleSet()) == 0) {
        throw MissingDebugInfoException();
    }

    llvm_utils::setBBIds(*LLVM_MODULE(SVF::LLVMModuleSet::getLLVMModuleSet()));

    SVF::PAGBuilder builder;
    pag = unique_ptr<SVF::PAG>(builder.build(svfModule));
}

vector<FuncInfo> Inspector::getFuncInfos() {
    SVF::Andersen *ander = SVF::AndersenWaveDiff::createAndersenWaveDiff(pag.get());
    SVF::PTACallGraph *callGraph = ander->getPTACallGraph();

    vector<FuncInfo> funcInfos;

    for (auto callNode : *callGraph) {
        const llvm::Function &llvmFunc = *callNode.second->getFunction()->getLLVMFun();

        if (!llvmFunc.isDeclaration()) {
            auto optLineNumbers = llvm_utils::getFunctionLines(llvmFunc);

            if (optLineNumbers.has_value()) {
                string name = llvmFunc.getName().str();
                string filename = llvm_utils::getFilename(llvmFunc);
                Lines lineNumbers = optLineNumbers.value();
                LineRange lineRange = llvm_utils::computeRange(lineNumbers);
                bool reachableFromMain = callNode.second->isReachableFromProgEntry();

                set<BBInfo> blockInfos;

                for (auto &bb : llvmFunc) {
                    auto optBBLineNumbers = llvm_utils::getBBLines(bb);

                    if (optBBLineNumbers.has_value()) {
                        BBId id = llvm_utils::getBBId(bb).value();
                        Lines bbLines = optBBLineNumbers.value();
                        LineRange bbLineRange = llvm_utils::computeRange(bbLines);

                        blockInfos.insert(BBInfo(id, bbLines, bbLineRange));
                    }
                }

                funcInfos.emplace_back(FuncInfo(name, filename, lineNumbers, lineRange, reachableFromMain, blockInfos));
            }
        }
    }

    return funcInfos;
}

map<BBId, set<BBId>> Inspector::getICFGInfos() {
    SVF::ICFG *icfg = pag->getICFG();

    map<BBId, set<BBId>> icfgInfos;

    for (auto nodeInfo : *icfg) {
        SVF::ICFGNode *srcNode = nodeInfo.second;

        if (srcNode->getBB() != nullptr) {
            BBId srcBBId = llvm_utils::getBBId(*srcNode->getBB()).value();

            for (auto edge : srcNode->getOutEdges()) {
                // Assert that the source node ID matches the edge source node ID
                assert(srcNode->getId() == edge->getSrcNode()->getId());

                SVF::ICFGNode *dstNode = edge->getDstNode();

                if (dstNode->getBB() != nullptr) {
                    BBId dstBBId = llvm_utils::getBBId(*dstNode->getBB()).value();

                    // TODO: Only allow "srcBBId == dstBBId" if recursive function call or loop iteration
                    icfgInfos[srcBBId].insert(dstBBId);
                }
            }
        }
    }

    return icfgInfos;
}
