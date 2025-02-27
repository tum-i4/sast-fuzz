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

#include <gtest/gtest.h>

#include <sfi/func_info.h>
#include <sfi/types.h>

using namespace testing;
using namespace sfi;

TEST(FuncInfoTestSuite, ConstructorAndGettersTest) {
    // Arrange + Act
    std::string name = "foo";
    std::string filename = "bar.c";
    Lines lineNumbers = {10, 11, 12};
    LineRange lineRange = {10, 12};
    bool reachableFromMain = true;
    std::set<BBInfo> blockInfos;

    FuncInfo funcInfo(name, filename, lineNumbers, lineRange, reachableFromMain, blockInfos);

    // Assert
    ASSERT_EQ(funcInfo.getName(), name);
    ASSERT_EQ(funcInfo.getFilename(), filename);
    ASSERT_EQ(funcInfo.getLineNumbers(), lineNumbers);
    ASSERT_EQ(funcInfo.getLineRange(), lineRange);
    ASSERT_EQ(funcInfo.isReachableFromMain(), reachableFromMain);
    ASSERT_EQ(funcInfo.getBlockInfos(), blockInfos);
}

TEST(FuncInfoTestSuite, EqualityOperatorTest) {
    // Arrange + Act
    std::string name = "foo";
    std::string filename = "bar.c";
    Lines lineNumbers = {10, 11, 12};
    LineRange lineRange = {10, 12};
    bool reachableFromMain = true;
    std::set<BBInfo> blockInfos = {
            BBInfo(1, {10, 11}, {10, 11}),
            BBInfo(2, {12}, {12, 12}),
    };

    FuncInfo funcInfo1(name, filename, lineNumbers, lineRange, reachableFromMain, blockInfos);
    FuncInfo funcInfo2(name, filename, lineNumbers, lineRange, reachableFromMain, blockInfos);

    // Assert
    ASSERT_EQ(funcInfo1, funcInfo2);
}

TEST(FuncInfoTestSuite, InequalityOperatorTest) {
    // Arrange + Act
    std::string name = "foo";
    std::string filename = "bar.c";
    Lines lineNumbers = {10, 11, 12};
    LineRange lineRange = {10, 12};
    bool reachableFromMain = true;
    std::set<BBInfo> blockInfos = {
            BBInfo(1, {10, 11}, {10, 11}),
            BBInfo(2, {12}, {12, 12}),
    };
    std::set<BBInfo> differentBlockInfos = {
            BBInfo(3, {10, 11}, {10, 11}),
            BBInfo(4, {12}, {12, 12}),
    };

    FuncInfo funcInfo1(name, filename, lineNumbers, lineRange, reachableFromMain, blockInfos);
    FuncInfo funcInfo2(name, filename, lineNumbers, lineRange, reachableFromMain, differentBlockInfos);

    // Assert
    ASSERT_NE(funcInfo1, funcInfo2);
}