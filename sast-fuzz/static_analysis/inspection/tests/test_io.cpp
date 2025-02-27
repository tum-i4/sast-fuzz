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

#include <gmock/gmock.h>

#include <filesystem>
#include <fstream>

#include <gtest/gtest.h>

#include <sfi/io.h>

using namespace testing;
using namespace sfi;

namespace fs = std::filesystem;

class IOTestSuite : public Test {
  protected:
    fs::path tempFile;

    void SetUp() override {
        tempFile = fs::temp_directory_path() / "test.txt";
        if (fs::exists(tempFile)) {
            fs::remove(tempFile);
        }
    }

    void TearDown() override {
        if (fs::exists(tempFile)) {
            fs::remove(tempFile);
        }
    }
};

TEST_F(IOTestSuite, ReadyEmptyFile) {
    std::ofstream ofs(tempFile);
    ofs.close();
    auto actual = io::readFile(tempFile);
    ASSERT_TRUE(actual.empty());
}

TEST_F(IOTestSuite, WriteAndRead) {
    io::writeFile(tempFile, "foo");
    ASSERT_TRUE(fs::exists(tempFile));
    auto actual = io::readFile(tempFile);
    ASSERT_EQ(actual, "foo");
}