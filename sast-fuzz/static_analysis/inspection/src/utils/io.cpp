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

#include <fstream>
#include <iterator>

#include <sfi/io.h>

using namespace std;
using namespace sfi;

string io::readFile(const string &filepath) {
    string text;
    ifstream inputFile(filepath);

    if (inputFile.is_open()) {
        text = string(istreambuf_iterator<char>(inputFile), istreambuf_iterator<char>());
        inputFile.close();
    }

    return text;
}

void io::writeFile(const string &filepath, const string &text) {
    ofstream outputFile(filepath);

    if (outputFile.is_open()) {
        outputFile << text;
        outputFile.close();
    }
}
