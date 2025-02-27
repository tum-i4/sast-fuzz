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

#ifndef SFI_LLVM_UTILS_H
#define SFI_LLVM_UTILS_H

#include <string>

#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Module.h>

#include <sfi/types.h>

namespace sfi::llvm_utils {

/**
 * Computes the range of a given set of line numbers.
 *
 * @param lineNumbers Set of line numbers.
 * @return Tuple containing the minimum and maximum line numbers.
 */
LineRange computeRange(const Lines &lineNumbers);

/**
 * Gets the filename associated with a given function.
 *
 * @param func Function object.
 * @return Filename associated with the function.
 */
std::string getFilename(const llvm::Function &func);

/**
 * Sets a unique ID for a given basic block.
 *
 * @param bb Basic block object.
 * @param id Unique ID to set.
 */
void setBBId(llvm::BasicBlock &bb, BBId id);

/**
 * Sets unique IDs for all basic blocks in a given module.
 *
 * @param mod Module object.
 */
void setBBIds(llvm::Module &mod);

/**
 * Gets the ID of a given basic block.
 *
 * @param bb Basic block object.
 * @return Optional containing the ID of the basic block, or nullopt if the basic block does not have an ID set.
 */
std::optional<BBId> getBBId(const llvm::BasicBlock &bb);

/**
 * Gets the line numbers associated with a given basic block.
 *
 * @param bb Basic block object.
 * @return Optional containing the set of line numbers associated with the basic block, or nullopt if no line numbers
 * were found.
 */
std::optional<Lines> getBBLines(const llvm::BasicBlock &bb);

/**
 * Gets the line range associated with a given basic block.
 *
 * @param bb Basic block object.
 * @return Optional containing the line range associated with the basic block, or nullopt if no line numbers were found.
 */
std::optional<LineRange> getBBLineRange(const llvm::BasicBlock &bb);

/**
 * Gets the line numbers associated with a given function.
 *
 * @param func Function object.
 * @return Optional containing the set of line numbers associated with the function, or nullopt if no line numbers were
 * found.
 */
std::optional<Lines> getFunctionLines(const llvm::Function &func);

/**
 * Gets the line range associated with a given function.
 *
 * @param func Function object.
 * @return Optional containing the line range associated with the function, or nullopt if no line numbers were found.
 */
std::optional<LineRange> getFunctionLineRange(const llvm::Function &func);

}  // namespace sfi::llvm_utils

#endif  // SFI_LLVM_UTILS_H
