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

#ifndef SFI_IO_H
#define SFI_IO_H

#include <string>

namespace sfi::io {

/**
 * Reads the contents of a file into a string.
 *
 * @param filepath The path to the file to read.
 * @return The contents of the file as a string, or an empty string if the file could not be opened.
 */
std::string readFile(const std::string &filepath);

/**
 * Writes a string to a file.
 *
 * @param filepath The path to the file to write.
 * @param text The string to write to the file.
 */
void writeFile(const std::string &filepath, const std::string &text);

}  // namespace sfi::io

#endif  // SFI_IO_H
