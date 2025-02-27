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

#ifndef SFI_INSPECTOR_H
#define SFI_INSPECTOR_H

#include <exception>
#include <map>
#include <string>
#include <vector>

#include <SVF-FE/PAGBuilder.h>

#include <sfi/func_info.h>

namespace sfi {

class MissingDebugInfoException : public std::exception {
  private:
    std::string message;

  public:
    MissingDebugInfoException() : message("ERROR: LLVM module doesn't contain debug information!") {}

    explicit MissingDebugInfoException(const std::string &message) : message(message) {}

    [[nodiscard]] const char *what() const noexcept override { return message.c_str(); }
};

class Inspector {
  private:
    std::unique_ptr<SVF::PAG> pag;

  public:
    /**
     * Constructor for Inspector class
     *
     * Builds an SVFModule object from the bitcode file provided as a parameter, then checks if the DWARF version of the
     * LLVM module is 0 to ensure debug information is present. If debug information is missing, a
     * MissingDebugInfoException is thrown. The basic block IDs for the LLVM module are set and a PAG (Pointer Analysis
     * Graph) object is built from the SVFModule object using a PAGBuilder.
     *
     * @param bitcodeFile The path to the LLVM bitcode file to be analyzed
     * @throw MissingDebugInfoException If debug information is missing
     * @throw std::runtime_error If an error occurs during PAG construction
     */
    explicit Inspector(std::string bitcodeFile) noexcept(false);

    /**
     * Retrieves information about functions in the program
     *
     * This function uses pointer analysis to extract information about functions in the program, including their names,
     * filenames, line numbers, and if they are reachable from the main function. For each function it also extracts
     * basic block information such as IDs, line numbers, and ranges, for each function. The function returns a vector
     * of FuncInfo objects that contain the extracted information.
     *
     * @return A vector of FuncInfo objects containing information about each function in the program
     */
    std::vector<sfi::FuncInfo> getFuncInfos();

    /**
     * Returns a map that represents the inter-procedural control-flow graph (iCFG) of the program.
     *
     * This function retrieves the iCFG from the pointer analysis graph (PAG) of the program and constructs a map that
     * represents the iCFG. Each key of the map is a basic block ID of a source node, and its value is a set of basic
     * block IDs of destination nodes reachable from the source node via the control flow graph.
     *
     * @return A map that represents the iCFG of the program.
     */
    std::map<sfi::BBId, std::set<sfi::BBId>> getICFGInfos();
};

}  // namespace sfi

#endif  // SFI_INSPECTOR_H
