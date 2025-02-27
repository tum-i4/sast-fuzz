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

#include <filesystem>
#include <iostream>
#include <set>

#include <llvm/IR/DebugInfo.h>

#include <sfi/llvm_utils.h>

#define BLOCK_ID_KEY "sast-fuzz.block.id"
#define BLOCK_ENTRY(bb) ((bb).getFirstNonPHI())

using namespace std;
using namespace std::filesystem;
using namespace llvm;
using namespace sfi;

LineRange llvm_utils::computeRange(const Lines &lineNumbers) {
    LineNumber min = *min_element(lineNumbers.begin(), lineNumbers.end());
    LineNumber max = *max_element(lineNumbers.begin(), lineNumbers.end());

    return LineRange(min, max);
}

string llvm_utils::getFilename(const Function &func) {
    return path(func.getSubprogram()->getFilename().str()).filename();
}

void llvm_utils::setBBId(BasicBlock &bb, BBId id) {
    Instruction *inst = BLOCK_ENTRY(bb);
    LLVMContext &C = inst->getContext();

    MDNode *node = MDNode::get(C, MDString::get(C, to_string(id)));

    inst->setMetadata(BLOCK_ID_KEY, node);
}

void llvm_utils::setBBIds(Module &mod) {
    BBId id = 0;
    for (auto &func : mod) {
        for (auto &bb : func) {
            setBBId(bb, id++);
        }
    }
}

std::optional<BBId> llvm_utils::getBBId(const BasicBlock &bb) {
    const Instruction *inst = BLOCK_ENTRY(bb);

    if (!inst->hasMetadata(BLOCK_ID_KEY)) {
        return nullopt;
    }

    auto temp = cast<MDString>(inst->getMetadata(BLOCK_ID_KEY)->getOperand(0));
    return stoul(temp->getString().str());
}

optional<Lines> llvm_utils::getBBLines(const BasicBlock &bb) {
    Lines lineNumbers;

    const Function *parentFunc = bb.getParent();

    for (auto &inst : bb) {
        auto &debugLoc = inst.getDebugLoc();
        if (debugLoc) {
            LineNumber line = debugLoc.getLine();
            if (line > 0) {
                // assert(line >= parentFunc->getSubprogram()->getLine() &&
                //        "ERROR: One of the analyzed instructions is located outside the corresponding function, e.g.
                //        in " "a C macro, and the passed bitcode file was not compiled with '-g -O0 -fno-inline'. In
                //        this " "case, we cannot reliably determine the line range of the function!");

                LineNumber firstFuncLine = parentFunc->getSubprogram()->getLine();

                if (line >= firstFuncLine) {
                    lineNumbers.insert(line);
                } else {
                    cout << "INFO: " << llvm_utils::getFilename(*parentFunc) << ":" << parentFunc->getName().str()
                         << ": Analyzed line is out of function scope (line = " << line
                         << ", function-begin = " << firstFuncLine << ")!" << endl;
                }
            }
        }
    }

    if (lineNumbers.empty()) {
        return nullopt;
    } else {
        return lineNumbers;
    }
}

optional<LineRange> llvm_utils::getBBLineRange(const BasicBlock &bb) {
    auto optLines = getBBLines(bb);

    if (!optLines.has_value()) {
        return nullopt;
    } else {
        Lines lineNumbers = optLines.value();

        return computeRange(lineNumbers);
    }
}

optional<Lines> llvm_utils::getFunctionLines(const Function &func) {
    assert(!func.isDeclaration());

    if (!func.hasMetadata()) {
        return nullopt;
    }

    Lines lineNumbers;

    for (auto &bb : func) {
        auto optLines = getBBLines(bb);

        if (optLines.has_value()) {
            lineNumbers.merge(optLines.value());
        }
    }

    if (lineNumbers.empty()) {
        return nullopt;
    } else {
        return lineNumbers;
    }
}

optional<LineRange> llvm_utils::getFunctionLineRange(const Function &func) {
    auto optLines = getFunctionLines(func);

    if (!optLines.has_value()) {
        return nullopt;
    } else {
        Lines lineNumbers = optLines.value();

        return computeRange(lineNumbers);
    }
}
