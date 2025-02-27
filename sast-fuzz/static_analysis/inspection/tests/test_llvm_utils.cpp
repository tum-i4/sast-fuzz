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
#include <map>
#include <set>

#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/Support/SourceMgr.h>

#include <gtest/gtest.h>

#include <sfi/llvm_utils.h>
#include <sfi/types.h>

using namespace testing;
using namespace llvm;
using namespace sfi;

namespace fs = std::filesystem;

class LLVMUtilsTestSuite : public Test {
  protected:
    std::unique_ptr<Module> llvmModule;
    std::string bitcodeFile = "./data/llvm_bc/quicksort.bc";

    template <typename Container, typename T> bool contains(const Container &container, const T &element) {
        return std::find(container.begin(), container.end(), element) != container.end();
    }

    void SetUp() override {
        LLVMContext ctx;
        SMDiagnostic error;

        llvmModule = parseIRFile(bitcodeFile, error, ctx);

        if (llvmModule == nullptr) {
            error.print("LLVMUtilsTestSuite", errs());
            FAIL();
        }
    }

    void TearDown() override { llvmModule.release(); }
};

TEST_F(LLVMUtilsTestSuite, GetFilenameTest) {
    // Arrange
    std::string expected = fs::path(bitcodeFile).filename();

    for (auto &func : *llvmModule) {
        // Act
        auto actual = llvm_utils::getFilename(func);

        // Assert
        ASSERT_EQ(expected, actual);
    }
}

TEST_F(LLVMUtilsTestSuite, SetGetBBIdTest) {
    // Arrange
    BBId expected = 42;

    for (auto &func : *llvmModule) {
        for (auto &bb : func) {
            // Act
            llvm_utils::setBBId(bb, expected);

            auto actual = llvm_utils::getBBId(bb);

            // Assert
            ASSERT_TRUE(actual.has_value());
            ASSERT_EQ(expected, actual.value());
        }
    }
}

TEST_F(LLVMUtilsTestSuite, UniqueBBIdsTest) {
    // Arrange + Act
    llvm_utils::setBBIds(*llvmModule);

    std::vector<BBId> actual;
    for (auto &func : *llvmModule) {
        for (auto &bb : func) {
            actual.emplace_back(llvm_utils::getBBId(bb).value());
        }
    }

    std::set<BBId> expected(actual.begin(), actual.end());

    // Assert
    ASSERT_TRUE(expected.size() == actual.size());
}

TEST_F(LLVMUtilsTestSuite, GetFunctionLineRange) {
    // Arrange
    std::map<std::string, std::map<std::string, std::set<LineNumber>>> expected = {
            {"swap", {{"start", {6, 7}}, {"end", {9, 10}}}},
            {"partition", {{"start", {13, 14, 15}}, {"end", {37, 38}}}},
            {"quickSort", {{"start", {40, 41}}, {"end", {51, 52, 53}}}},
            {"printArray", {{"start", {56, 57}}, {"end", {60, 61}}}},
            {"main", {{"start", {64, 65}}, {"end", {76, 77}}}},
    };

    for (auto &func : *llvmModule) {
        std::string funcName = func.getName().str();

        // Act
        auto actual = llvm_utils::getFunctionLineRange(func);

        // Assert
        ASSERT_TRUE(actual.has_value());

        ASSERT_TRUE(contains(expected[funcName]["start"], actual.value().first));
        ASSERT_TRUE(contains(expected[funcName]["end"], actual.value().second));
    }
}