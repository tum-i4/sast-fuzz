# Copyright 2023-2024 XXX
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import unittest
from pathlib import Path

from sfa.analysis import SASTFlag, SASTFlags
from sfa.analysis.filter import ReachabilityFilter


class TestReachabilityFilter(unittest.TestCase):
    def setUp(self) -> None:
        inspec_file = Path(__file__).parent / "data" / "sfi" / "quicksort.json"
        self.filter = ReachabilityFilter(inspec_file)

    def test_filter_correct(self) -> None:
        # Arrange
        flags = SASTFlags()
        flags.add(SASTFlag("tool1", "quicksort.c", 29, "-"))
        flags.add(SASTFlag("tool2", "quicksort.c", 48, "-"))
        flags.add(SASTFlag("tool3", "quicksort.c", 60, "-"))
        flags.add(SASTFlag("tool4", "quicksort.c", 76, "-"))

        # Act
        actual = self.filter.filter(flags)

        # Assert
        self.assertEqual(flags, actual)

    def test_filter_scope_one_out(self) -> None:
        # Arrange
        flag1 = SASTFlag("tool1", "quicksort.c", 29, "-")
        flag2 = SASTFlag("tool2", "quicksort.c", 39, "-")  # Outside function scope
        flag3 = SASTFlag("tool3", "quicksort.c", 60, "-")
        flag4 = SASTFlag("tool4", "quicksort.c", 76, "-")

        flags = SASTFlags({flag1, flag2, flag3, flag4})

        expected = SASTFlags({flag1, flag3, flag4})

        # Act
        actual = self.filter.filter(flags)

        # Assert
        self.assertEqual(expected, actual)

    def test_filter_scope_all_out(self) -> None:
        # Arrange
        flag1 = SASTFlag("tool1", "quicksort.c", 11, "-")  # Outside function scope
        flag2 = SASTFlag("tool2", "quicksort.c", 39, "-")  # Outside function scope
        flag3 = SASTFlag("tool3", "quicksort.c", 54, "-")  # Outside function scope

        flags = SASTFlags({flag1, flag2, flag3})

        expected = SASTFlags()

        # Act
        actual = self.filter.filter(flags)

        # Assert
        self.assertEqual(expected, actual)

    def test_filter_dc(self) -> None:
        # Arrange
        flag1 = SASTFlag("tool1", "quicksort.c", 80, "-")  # Dead code
        flag2 = SASTFlag("tool2", "quicksort.c", 82, "-")  # Dead code

        flags = SASTFlags({flag1, flag2})

        expected = SASTFlags()

        # Act
        actual = self.filter.filter(flags)

        # Assert
        self.assertEqual(expected, actual)

    def test_filter_scope_dc(self) -> None:
        # Arrange
        flag1 = SASTFlag("tool1", "quicksort.c", 29, "-")
        flag2 = SASTFlag("tool2", "quicksort.c", 39, "-")  # Outside function scope
        flag3 = SASTFlag("tool3", "quicksort.c", 60, "-")
        flag4 = SASTFlag("tool4", "quicksort.c", 80, "-")  # Dead code

        flags = SASTFlags({flag1, flag2, flag3, flag4})

        expected = SASTFlags({flag1, flag3})

        # Act
        actual = self.filter.filter(flags)

        # Assert
        self.assertEqual(expected, actual)

    def test_filter_scope_dc_file(self) -> None:
        # Arrange
        flag1 = SASTFlag("tool1", "main.c", 29, "-")  # Wrong file
        flag2 = SASTFlag("tool2", "quicksort.c", 39, "-")  # Outside function scope
        flag3 = SASTFlag("tool3", "quicksort.c", 60, "-")
        flag4 = SASTFlag("tool4", "quicksort.c", 80, "-")  # Dead code

        flags = SASTFlags({flag1, flag2, flag3, flag4})

        expected = SASTFlags({flag3})

        # Act
        actual = self.filter.filter(flags)

        # Assert
        self.assertEqual(expected, actual)


if __name__ == "__main__":
    unittest.main()
