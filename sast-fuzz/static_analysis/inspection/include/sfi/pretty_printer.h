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

#ifndef SFI_PRETTY_PRINTER_H
#define SFI_PRETTY_PRINTER_H

#include <map>
#include <set>
#include <string>
#include <vector>

#include <sfi/func_info.h>
#include <sfi/io.h>

namespace sfi {

class Printer {
  public:
    /**
     * This pure virtual method is used to format the given vector of FuncInfo objects and map of BBId to BBId sets
     * (inter-procedural CFG) to a string representation.
     * @param funcInfos Vector of FuncInfo objects.
     * @param icfgInfos Map of BBId to BBId sets (iCFG).
     * @return A string representation of the formatted information.
     */
    virtual std::string format(std::vector<FuncInfo> &funcInfos,
                               std::optional<std::map<BBId, std::set<BBId>>> icfgInfos = std::nullopt) = 0;

    /**
     * This method writes the formatted information to a file.
     * @param filepath String containing the path of the file.
     * @param funcInfos Vector of FuncInfo objects.
     * @param icfgInfos Map of BBId to BBId sets (iCFG).
     */
    void printToFile(std::string &filepath,
                     std::vector<FuncInfo> &funcInfos,
                     std::optional<std::map<BBId, std::set<BBId>>> icfgInfos = std::nullopt) {
        io::writeFile(filepath, format(funcInfos, icfgInfos));
    }
};

class JSONPrinter : public Printer {
  public:
    /**
     * This method formats the given vector of FuncInfo objects and map of BBId to BBId sets (inter-procedural CFG) to
     * a JSON string.
     * @param funcInfos Vector of FuncInfo objects.
     * @param icfgInfos Map of BBId to BBId sets (iCFG).
     * @return A JSON string representation of the formatted information.
     */
    std::string format(std::vector<FuncInfo> &funcInfos,
                       std::optional<std::map<BBId, std::set<BBId>>> icfgInfos = std::nullopt) override;
};

}  // namespace sfi

#endif  // SFI_PRETTY_PRINTER_H
