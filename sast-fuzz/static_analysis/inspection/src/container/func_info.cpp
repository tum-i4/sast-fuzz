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

#include <sfi/func_info.h>

using namespace sfi;

FuncInfo::FuncInfo(const std::string &name,
                   const std::string &filename,
                   const Lines &lineNumbers,
                   const LineRange &lineRange,
                   bool reachableFromMain,
                   std::set<BBInfo> blockInfos)
    : name(name), filename(filename), lineNumbers(lineNumbers), lineRange(lineRange),
      reachableFromMain(reachableFromMain), blockInfos(std::move(blockInfos)) {}

const std::string &FuncInfo::getName() const { return name; }

const std::string &FuncInfo::getFilename() const { return filename; }

const Lines &FuncInfo::getLineNumbers() const { return lineNumbers; }

const LineRange &FuncInfo::getLineRange() const { return lineRange; }

bool FuncInfo::isReachableFromMain() const { return reachableFromMain; }

const std::set<BBInfo> &FuncInfo::getBlockInfos() const { return blockInfos; }

bool FuncInfo::operator==(const FuncInfo &rhs) const {
    return name == rhs.name && filename == rhs.filename && lineNumbers == rhs.lineNumbers &&
           lineRange == rhs.lineRange && reachableFromMain == rhs.reachableFromMain && blockInfos == rhs.blockInfos;
}

bool FuncInfo::operator!=(const FuncInfo &rhs) const { return !(rhs == *this); }
