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

#ifndef SFI_BB_INFO_H
#define SFI_BB_INFO_H

#include <ostream>

#include <sfi/types.h>

namespace sfi {

class BBInfo {
  private:
    BBId id;
    Lines lineNumbers;
    LineRange lineRange;

  public:
    /**
     * Constructor for BBInfo class.
     *
     * @param id The unique ID of the basic block.
     * @param lineNumbers The line numbers corresponding to the basic block.
     * @param lineRange The range of lines corresponding to the basic block.
     */
    BBInfo(BBId id, const Lines &lineNumbers, const LineRange &lineRange);

    /**
     * Returns the ID of the basic block.
     *
     * @return BBId The ID of the basic block.
     */
    [[nodiscard]] BBId getId() const;

    /**
     * Returns the line numbers corresponding to the basic block.
     *
     * @return const Lines& The line numbers corresponding to the basic block.
     */
    [[nodiscard]] const Lines &getLineNumbers() const;

    /**
     * Returns the range of lines corresponding to the basic block.
     *
     * @return const LineRange& The range of lines corresponding to the basic block.
     */
    [[nodiscard]] const LineRange &getLineRange() const;

    /**
     * Checks if two BBInfo objects are equal.
     *
     * @param rhs The BBInfo object to compare against.
     * @return true if the two BBInfo objects are equal, false otherwise.
     */
    bool operator==(const BBInfo &rhs) const;

    /**
     * Checks if two BBInfo objects are not equal.
     *
     * @param rhs The BBInfo object to compare against.
     * @return true if the two BBInfo objects are not equal, false otherwise.
     */
    bool operator!=(const BBInfo &rhs) const;

    /**
     * Checks if the ID of a BBInfo object is smaller than that of the other.
     *
     * @param rhs The BBInfo object to compare against.
     * @return true if the ID of this BBInfo object is less than that of the rhs object, false otherwise.
     */
    bool operator<(const BBInfo &rhs) const;
};

}  // namespace sfi

#endif  // SFI_BB_INFO_H
