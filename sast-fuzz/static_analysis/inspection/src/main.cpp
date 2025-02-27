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

#include <iostream>

#include <SVF-FE/LLVMUtil.h>

#include <sfi/inspector.h>
#include <sfi/pretty_printer.h>

using namespace std;
using namespace sfi;

static llvm::cl::opt<std::string> inputFile(llvm::cl::Positional, llvm::cl::desc("<input: LLVM bitcode file>"));

static llvm::cl::opt<std::string> outputFile(llvm::cl::Positional, llvm::cl::desc("<output: JSON file>"));

static llvm::cl::opt<bool> outputICFG ("icfg", llvm::cl::desc("Output inter-procedural CFG"));

int main(int argc, char **argv) {
    llvm::cl::ParseCommandLineOptions(argc, argv, "SASTFuzz Inspector (SFI)\n");

    if (inputFile.empty() || outputFile.empty()) {
        cerr << "ERROR: LLVM bitcode file and/or JSON output file not specified!" << endl;
        return 1;
    }

    try {
        JSONPrinter printer;
        Inspector inspector(inputFile);

        auto funcInfos = inspector.getFuncInfos();

        std::optional<std::map<BBId, std::set<BBId>>> icfgInfos;
        if (!outputICFG) {
            icfgInfos = nullopt;
        } else {
            icfgInfos = inspector.getICFGInfos();
        }

        printer.printToFile(outputFile, funcInfos, icfgInfos);

        return 0;

    } catch (MissingDebugInfoException &exception) {
        cerr << exception.what();
        return 1;
    }
}