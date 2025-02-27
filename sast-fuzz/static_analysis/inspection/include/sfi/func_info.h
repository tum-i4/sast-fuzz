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

#ifndef SFI_FUNC_INFO_H
#define SFI_FUNC_INFO_H

#include <ostream>
#include <set>
#include <string>

#include <sfi/bb_info.h>

namespace sfi {

class FuncInfo {
  private:
    std::string name;
    std::string filename;
    Lines lineNumbers;
    LineRange lineRange;
    bool reachableFromMain;
    std::set<BBInfo> blockInfos;

  public:
    /**
     * Constructor for FuncInfo class.
     *
     * @param name The name of the function.
     * @param filename The name of the file the function belongs to.
     * @param lineNumbers The line numbers corresponding to the function.
     * @param lineRange The range of lines corresponding to the function.
     * @param reachableFromMain Indicates if the function is reachable from the main function.
     * @param blockInfos A set of basic block information objects belonging to the function.
     */
    FuncInfo(const std::string &name,
             const std::string &filename,
             const Lines &lineNumbers,
             const LineRange &lineRange,
             bool reachableFromMain,
             std::set<BBInfo> blockInfos);

    /**
     * Returns the name of the function.
     *
     * @return const std::string& The name of the function.
     */
    [[nodiscard]] const std::string &getName() const;

    /**
     * Returns the name of the file the function belongs to.
     *
     * @return const std::string& The name of the file the function belongs to.
     */
    [[nodiscard]] const std::string &getFilename() const;

    /**
     * Returns the line numbers corresponding to the function.
     *
     * @return const Lines& The line numbers corresponding to the function.
     */
    [[nodiscard]] const Lines &getLineNumbers() const;

    /**
     * Returns the range of lines corresponding to the function.
     *
     * @return const LineRange& The range of lines corresponding to the function.
     */
    [[nodiscard]] const LineRange &getLineRange() const;

    /**
     * Checks if the function is reachable from the main function.
     *
     * @return true if the function is reachable from the main function, false otherwise.
     */
    [[nodiscard]] bool isReachableFromMain() const;

    /**
     * Returns a set of basic block information objects belonging to the function.
     *
     * @return const std::set<BBInfo>& A set of basic block information objects belonging to the function.
     */
    [[nodiscard]] const std::set<BBInfo> &getBlockInfos() const;

    /**
     * Checks if two FuncInfo objects are equal.
     *
     * @param rhs The FuncInfo object to compare against.
     * @return true if the two FuncInfo objects are equal, false otherwise.
     */
    bool operator==(const FuncInfo &rhs) const;

    /**
     * Checks if two FuncInfo objects are not equal.
     *
     * @param rhs The FuncInfo object to compare against.
     * @return true if the two FuncInfo objects are not equal, false otherwise.
     */
    bool operator!=(const FuncInfo &rhs) const;
};

}  // namespace sfi

#endif  // SFI_FUNC_INFO_H
