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
from typing import Set, Tuple

from sfa import ScoreWeights
from sfa.analysis import GroupedSASTFlag, SASTFlag, SASTFlags
from sfa.analysis.grouping import CONCAT_CHAR, BasicBlockGrouping, BasicBlockV2Grouping, FunctionGrouping


def unfold(flags: SASTFlags) -> Set[Tuple]:
    """
    Unfold SAST flags into a set of tuples (whose elements are partially also converted into sets) to avoid flaky tests
    due to ordering issues in 'flag.tool' and 'flag.vuln'.

    :param flags:
    :return:
    """
    return {
        (
            frozenset(flag.tool.split(CONCAT_CHAR)),
            flag.file,
            flag.line,
            frozenset(flag.vuln.split(CONCAT_CHAR)),
            flag.n_flg_lines,
            flag.n_all_lines,
            flag.n_run_tools,
            flag.n_all_tools,
            flag.score,
        )
        for flag in flags
        if isinstance(flag, GroupedSASTFlag)
    }


class TestBasicBlockGrouping(unittest.TestCase):
    def setUp(self) -> None:
        inspec_file = Path(__file__).parent / "data" / "sfi" / "quicksort.json"
        self.grouping = BasicBlockGrouping(inspec_file, ScoreWeights(0.5, 0.5))

    def test_group_same_bb(self) -> None:
        # Arrange
        flags = SASTFlags()
        flags.add(SASTFlag("tool1", "quicksort.c", 67, "vuln1"))  # Block 16
        flags.add(SASTFlag("tool2", "quicksort.c", 70, "vuln2"))  # Block 16
        flags.add(SASTFlag("tool3", "quicksort.c", 73, "vuln3"))  # Block 16

        expected = SASTFlags()
        expected.add(GroupedSASTFlag("tool1-tool2-tool3", "quicksort.c", 65, "vuln1:67-vuln2:70-vuln3:73", 3, 8, 3, 3, 0.688))

        # Act
        actual = self.grouping.group(flags)

        # Assert
        self.assertEqual(unfold(expected), unfold(actual))

    def test_group_two_bbs(self) -> None:
        # Arrange
        flags = SASTFlags()
        flags.add(SASTFlag("tool1", "quicksort.c", 67, "vuln1"))  # Block 16
        flags.add(SASTFlag("tool2", "quicksort.c", 19, "vuln2"))  # Block 1
        flags.add(SASTFlag("tool3", "quicksort.c", 73, "vuln3"))  # Block 16

        expected = SASTFlags()
        expected.add(GroupedSASTFlag("tool1-tool3", "quicksort.c", 65, "vuln1:67-vuln3:73", 2, 8, 2, 3, 0.458))
        expected.add(GroupedSASTFlag("tool2", "quicksort.c", 13, "vuln2:19", 1, 4, 1, 3, 0.292))

        # Act
        actual = self.grouping.group(flags)

        # Assert
        self.assertEqual(unfold(expected), unfold(actual))

    def test_group_three_bbs(self) -> None:
        # Arrange
        flags = SASTFlags()
        flags.add(SASTFlag("tool1", "quicksort.c", 47, "vuln1"))  # Block 9
        flags.add(SASTFlag("tool2", "quicksort.c", 19, "vuln2"))  # Block 1
        flags.add(SASTFlag("tool3", "quicksort.c", 73, "vuln3"))  # Block 16

        expected = SASTFlags()
        expected.add(GroupedSASTFlag("tool1", "quicksort.c", 45, "vuln1:47", 1, 4, 1, 3, 0.292))
        expected.add(GroupedSASTFlag("tool2", "quicksort.c", 13, "vuln2:19", 1, 4, 1, 3, 0.292))
        expected.add(GroupedSASTFlag("tool3", "quicksort.c", 65, "vuln3:73", 1, 8, 1, 3, 0.229))

        # Act
        actual = self.grouping.group(flags)

        # Assert
        self.assertEqual(unfold(expected), unfold(actual))

    def test_group_same_tool(self) -> None:
        # Arrange
        flags = SASTFlags()
        flags.add(SASTFlag("tool1", "quicksort.c", 67, "vuln1"))  # Block 16
        flags.add(SASTFlag("tool2", "quicksort.c", 19, "vuln2"))  # Block 1
        flags.add(SASTFlag("tool1", "quicksort.c", 73, "vuln3"))  # Block 16

        expected = SASTFlags()
        expected.add(GroupedSASTFlag("tool1", "quicksort.c", 65, "vuln1:67-vuln3:73", 2, 8, 1, 2, 0.375))
        expected.add(GroupedSASTFlag("tool2", "quicksort.c", 13, "vuln2:19", 1, 4, 1, 2, 0.375))

        # Act
        actual = self.grouping.group(flags)

        # Assert
        self.assertEqual(unfold(expected), unfold(actual))

    def test_group_same_vuln(self) -> None:
        # Arrange
        flags = SASTFlags()
        flags.add(SASTFlag("tool1", "quicksort.c", 67, "vuln1"))  # Block 16
        flags.add(SASTFlag("tool2", "quicksort.c", 19, "vuln2"))  # Block 1
        flags.add(SASTFlag("tool3", "quicksort.c", 67, "vuln1"))  # Block 16

        expected = SASTFlags()
        expected.add(GroupedSASTFlag("tool1-tool3", "quicksort.c", 65, "vuln1:67", 1, 8, 2, 3, 0.396))
        expected.add(GroupedSASTFlag("tool2", "quicksort.c", 13, "vuln2:19", 1, 4, 1, 3, 0.292))

        # Act
        actual = self.grouping.group(flags)

        # Assert
        self.assertEqual(unfold(expected), unfold(actual))

    def test_group_diff_vuln_same_line(self) -> None:
        # Arrange
        flags = SASTFlags()
        flags.add(SASTFlag("tool1", "quicksort.c", 67, "vuln1"))  # Block 16
        flags.add(SASTFlag("tool2", "quicksort.c", 19, "vuln2"))  # Block 1
        flags.add(SASTFlag("tool3", "quicksort.c", 67, "vuln3"))  # Block 16

        expected = SASTFlags()
        expected.add(GroupedSASTFlag("tool1-tool3", "quicksort.c", 65, "vuln1:67-vuln3:67", 1, 8, 2, 3, 0.396))
        expected.add(GroupedSASTFlag("tool2", "quicksort.c", 13, "vuln2:19", 1, 4, 1, 3, 0.292))

        # Act
        actual = self.grouping.group(flags)

        # Assert
        self.assertEqual(unfold(expected), unfold(actual))

    def test_group_scope_func(self) -> None:
        # Arrange
        flags = SASTFlags()
        flags.add(SASTFlag("tool1", "quicksort.c", 54, "vuln1"))  # Outside of function(s)
        flags.add(SASTFlag("tool2", "quicksort.c", 19, "vuln2"))  # Block 1
        flags.add(SASTFlag("tool3", "quicksort.c", 67, "vuln3"))  # Block 16

        expected = SASTFlags()
        expected.add(GroupedSASTFlag("tool2", "quicksort.c", 13, "vuln2:19", 1, 4, 1, 3, 0.292))
        expected.add(GroupedSASTFlag("tool3", "quicksort.c", 65, "vuln3:67", 1, 8, 1, 3, 0.229))

        # Act
        actual = self.grouping.group(flags)

        # Assert
        self.assertEqual(unfold(expected), unfold(actual))

    def test_group_scope_file(self) -> None:
        # Arrange
        flags = SASTFlags()
        flags.add(SASTFlag("tool1", "main.c", 67, "vuln1"))  # Wrong file
        flags.add(SASTFlag("tool2", "quicksort.c", 19, "vuln2"))  # Block 1
        flags.add(SASTFlag("tool3", "quicksort.c", 73, "vuln3"))  # Block 16

        expected = SASTFlags()
        expected.add(GroupedSASTFlag("tool2", "quicksort.c", 13, "vuln2:19", 1, 4, 1, 3, 0.292))
        expected.add(GroupedSASTFlag("tool3", "quicksort.c", 65, "vuln3:73", 1, 8, 1, 3, 0.229))

        # Act
        actual = self.grouping.group(flags)

        # Assert
        self.assertEqual(unfold(expected), unfold(actual))


class TestBasicBlockV2Grouping(unittest.TestCase):
    def setUp(self) -> None:
        inspec_file = Path(__file__).parent / "data" / "sfi" / "quicksort.json"
        self.grouping = BasicBlockV2Grouping(inspec_file, ScoreWeights(0.5, 0.5))

    def test_group_same_func(self) -> None:
        # Arrange
        flags = SASTFlags()
        flags.add(SASTFlag("tool1", "quicksort.c", 58, "vuln1"))  # Function "printArray", block 13
        flags.add(SASTFlag("tool2", "quicksort.c", 59, "vuln2"))  # Function "printArray", block 13
        flags.add(SASTFlag("tool3", "quicksort.c", 60, "vuln3"))  # Function "printArray", block 15

        expected = SASTFlags()
        expected.add(GroupedSASTFlag("tool1-tool2", "quicksort.c", 58, "vuln1:58-vuln2:59", 3, 6, 3, 3, 0.75))
        expected.add(GroupedSASTFlag("tool3", "quicksort.c", 60, "vuln3:60", 3, 6, 3, 3, 0.75))

        # Act
        actual = self.grouping.group(flags)

        # Assert
        self.assertEqual(unfold(expected), unfold(actual))

    def test_group_two_funcs(self) -> None:
        # Arrange
        flags = SASTFlags()
        flags.add(SASTFlag("tool1", "quicksort.c", 58, "vuln1"))  # Function "printArray", block 13
        flags.add(SASTFlag("tool2", "quicksort.c", 73, "vuln2"))  # Function "main", block 16
        flags.add(SASTFlag("tool3", "quicksort.c", 60, "vuln3"))  # Function "printArray", block 15

        expected = SASTFlags()
        expected.add(GroupedSASTFlag("tool1", "quicksort.c", 58, "vuln1:58", 2, 6, 2, 3, 0.5))
        expected.add(GroupedSASTFlag("tool2", "quicksort.c", 65, "vuln2:73", 1, 8, 1, 3, 0.229))
        expected.add(GroupedSASTFlag("tool3", "quicksort.c", 60, "vuln3:60", 2, 6, 2, 3, 0.5))

        # Act
        actual = self.grouping.group(flags)

        # Assert
        self.assertEqual(unfold(expected), unfold(actual))

    def test_group_three_funcs(self) -> None:
        # Arrange
        flags = SASTFlags()
        flags.add(SASTFlag("tool1", "quicksort.c", 68, "vuln1"))  # Function "main", block 16
        flags.add(SASTFlag("tool2", "quicksort.c", 56, "vuln2"))  # Function "printArray", block 11
        flags.add(SASTFlag("tool3", "quicksort.c", 36, "vuln3"))  # Function "partition", block 7

        expected = SASTFlags()
        expected.add(GroupedSASTFlag("tool1", "quicksort.c", 65, "vuln1:68", 1, 8, 1, 3, 0.229))
        expected.add(GroupedSASTFlag("tool2", "quicksort.c", 56, "vuln2:56", 1, 6, 1, 3, 0.25))
        expected.add(GroupedSASTFlag("tool3", "quicksort.c", 34, "vuln3:36", 1, 11, 1, 3, 0.212))

        # Act
        actual = self.grouping.group(flags)

        # Assert
        self.assertEqual(unfold(expected), unfold(actual))

    def test_group_same_tool(self) -> None:
        # Arrange
        flags = SASTFlags()
        flags.add(SASTFlag("tool1", "quicksort.c", 48, "vuln1"))  # Function "quickSort", block 9
        flags.add(SASTFlag("tool2", "quicksort.c", 67, "vuln2"))  # Function "main", block 16
        flags.add(SASTFlag("tool1", "quicksort.c", 50, "vuln3"))  # Function "quickSort", block 9

        expected = SASTFlags()
        expected.add(GroupedSASTFlag("tool1", "quicksort.c", 45, "vuln1:48-vuln3:50", 2, 7, 1, 2, 0.393))
        expected.add(GroupedSASTFlag("tool2", "quicksort.c", 65, "vuln2:67", 1, 8, 1, 2, 0.312))

        # Act
        actual = self.grouping.group(flags)

        # Assert
        self.assertEqual(unfold(expected), unfold(actual))

    def test_group_same_vuln(self) -> None:
        # Arrange
        flags = SASTFlags()
        flags.add(SASTFlag("tool1", "quicksort.c", 48, "vuln1"))  # Function "quickSort", block 9
        flags.add(SASTFlag("tool2", "quicksort.c", 67, "vuln2"))  # Function "main", block 16
        flags.add(SASTFlag("tool3", "quicksort.c", 48, "vuln1"))  # Function "quickSort", block 9

        expected = SASTFlags()
        expected.add(GroupedSASTFlag("tool1-tool3", "quicksort.c", 45, "vuln1:48", 1, 7, 2, 3, 0.405))
        expected.add(GroupedSASTFlag("tool2", "quicksort.c", 65, "vuln2:67", 1, 8, 1, 3, 0.229))

        # Act
        actual = self.grouping.group(flags)

        # Assert
        self.assertEqual(unfold(expected), unfold(actual))

    def test_group_diff_vuln_same_line(self) -> None:
        # Arrange
        flags = SASTFlags()
        flags.add(SASTFlag("tool1", "quicksort.c", 48, "vuln1"))  # Function "quickSort", block 9
        flags.add(SASTFlag("tool2", "quicksort.c", 27, "vuln2"))  # Function "partition", block 4
        flags.add(SASTFlag("tool3", "quicksort.c", 48, "vuln3"))  # Function "quickSort", block 9

        expected = SASTFlags()
        expected.add(GroupedSASTFlag("tool1-tool3", "quicksort.c", 45, "vuln1:48-vuln3:48", 1, 7, 2, 3, 0.405))
        expected.add(GroupedSASTFlag("tool2", "quicksort.c", 26, "vuln2:27", 1, 11, 1, 3, 0.212))

        # Act
        actual = self.grouping.group(flags)

        # Assert
        self.assertEqual(unfold(expected), unfold(actual))

    def test_group_scope_func(self) -> None:
        # Arrange
        flags = SASTFlags()
        flags.add(SASTFlag("tool1", "quicksort.c", 54, "vuln1"))  # Outside of function(s)
        flags.add(SASTFlag("tool2", "quicksort.c", 60, "vuln2"))  # Function "printArray", block 15
        flags.add(SASTFlag("tool3", "quicksort.c", 67, "vuln3"))  # Function "main", block 16

        expected = SASTFlags()
        expected.add(GroupedSASTFlag("tool2", "quicksort.c", 60, "vuln2:60", 1, 6, 1, 3, 0.25))
        expected.add(GroupedSASTFlag("tool3", "quicksort.c", 65, "vuln3:67", 1, 8, 1, 3, 0.229))

        # Act
        actual = self.grouping.group(flags)

        # Assert
        self.assertEqual(unfold(expected), unfold(actual))

    def test_group_scope_file(self) -> None:
        # Arrange
        flags = SASTFlags()
        flags.add(SASTFlag("tool1", "main.c", 67, "vuln1"))  # Wrong file
        flags.add(SASTFlag("tool2", "quicksort.c", 60, "vuln2"))  # Function "printArray", block 15
        flags.add(SASTFlag("tool3", "quicksort.c", 67, "vuln3"))  # Function "main", block 16

        expected = SASTFlags()
        expected.add(GroupedSASTFlag("tool2", "quicksort.c", 60, "vuln2:60", 1, 6, 1, 3, 0.25))
        expected.add(GroupedSASTFlag("tool3", "quicksort.c", 65, "vuln3:67", 1, 8, 1, 3, 0.229))

        # Act
        actual = self.grouping.group(flags)

        # Assert
        self.assertEqual(unfold(expected), unfold(actual))


class TestFunctionGrouping(unittest.TestCase):
    def setUp(self) -> None:
        inspec_file = Path(__file__).parent / "data" / "sfi" / "quicksort.json"
        self.grouping = FunctionGrouping(inspec_file, ScoreWeights(0.5, 0.5))

    def test_group_same_func(self) -> None:
        # Arrange
        flags = SASTFlags()
        flags.add(SASTFlag("tool1", "quicksort.c", 58, "vuln1"))  # Function "printArray"
        flags.add(SASTFlag("tool2", "quicksort.c", 59, "vuln2"))  # Function "printArray"
        flags.add(SASTFlag("tool3", "quicksort.c", 60, "vuln3"))  # Function "printArray"

        expected = SASTFlags()
        expected.add(GroupedSASTFlag("tool1-tool2-tool3", "quicksort.c", (56 + 1), "vuln1:58-vuln2:59-vuln3:60", 3, 6, 3, 3, 0.75))

        # Act
        actual = self.grouping.group(flags)

        # Assert
        self.assertEqual(unfold(expected), unfold(actual))

    def test_group_two_funcs(self) -> None:
        # Arrange
        flags = SASTFlags()
        flags.add(SASTFlag("tool1", "quicksort.c", 58, "vuln1"))  # Function "printArray"
        flags.add(SASTFlag("tool2", "quicksort.c", 73, "vuln2"))  # Function "main"
        flags.add(SASTFlag("tool3", "quicksort.c", 60, "vuln3"))  # Function "printArray"

        expected = SASTFlags()
        expected.add(GroupedSASTFlag("tool1-tool3", "quicksort.c", (56 + 1), "vuln1:58-vuln3:60", 2, 6, 2, 3, 0.5))
        expected.add(GroupedSASTFlag("tool2", "quicksort.c", (65 + 1), "vuln2:73", 1, 8, 1, 3, 0.229))

        # Act
        actual = self.grouping.group(flags)

        # Assert
        self.assertEqual(unfold(expected), unfold(actual))

    def test_group_three_funcs(self) -> None:
        # Arrange
        flags = SASTFlags()
        flags.add(SASTFlag("tool1", "quicksort.c", 68, "vuln1"))  # Function "main"
        flags.add(SASTFlag("tool2", "quicksort.c", 57, "vuln2"))  # Function "printArray"
        flags.add(SASTFlag("tool3", "quicksort.c", 33, "vuln3"))  # Function "partition"

        expected = SASTFlags()
        expected.add(GroupedSASTFlag("tool1", "quicksort.c", (65 + 1), "vuln1:68", 1, 8, 1, 3, 0.229))
        expected.add(GroupedSASTFlag("tool2", "quicksort.c", (56 + 1), "vuln2:57", 1, 6, 1, 3, 0.25))
        expected.add(GroupedSASTFlag("tool3", "quicksort.c", (13 + 1), "vuln3:33", 1, 11, 1, 3, 0.212))

        # Act
        actual = self.grouping.group(flags)

        # Assert
        self.assertEqual(unfold(expected), unfold(actual))

    def test_group_same_tool(self) -> None:
        # Arrange
        flags = SASTFlags()
        flags.add(SASTFlag("tool1", "quicksort.c", 42, "vuln1"))  # Function "quickSort"
        flags.add(SASTFlag("tool2", "quicksort.c", 67, "vuln2"))  # Function "main"
        flags.add(SASTFlag("tool1", "quicksort.c", 50, "vuln3"))  # Function "quickSort"

        expected = SASTFlags()
        expected.add(GroupedSASTFlag("tool1", "quicksort.c", (40 + 1), "vuln1:42-vuln3:50", 2, 7, 1, 2, 0.393))
        expected.add(GroupedSASTFlag("tool2", "quicksort.c", (65 + 1), "vuln2:67", 1, 8, 1, 2, 0.312))

        # Act
        actual = self.grouping.group(flags)

        # Assert
        self.assertEqual(unfold(expected), unfold(actual))

    def test_group_same_vuln(self) -> None:
        # Arrange
        flags = SASTFlags()
        flags.add(SASTFlag("tool1", "quicksort.c", 42, "vuln1"))  # Function "quickSort"
        flags.add(SASTFlag("tool2", "quicksort.c", 67, "vuln2"))  # Function "main"
        flags.add(SASTFlag("tool3", "quicksort.c", 42, "vuln1"))  # Function "quickSort"

        expected = SASTFlags()
        expected.add(GroupedSASTFlag("tool1-tool3", "quicksort.c", (40 + 1), "vuln1:42", 1, 7, 2, 3, 0.405))
        expected.add(GroupedSASTFlag("tool2", "quicksort.c", (65 + 1), "vuln2:67", 1, 8, 1, 3, 0.229))

        # Act
        actual = self.grouping.group(flags)

        # Assert
        self.assertEqual(unfold(expected), unfold(actual))

    def test_group_diff_vuln_same_line(self) -> None:
        # Arrange
        flags = SASTFlags()
        flags.add(SASTFlag("tool1", "quicksort.c", 42, "vuln1"))  # Function "quickSort"
        flags.add(SASTFlag("tool2", "quicksort.c", 27, "vuln2"))  # Function "partition"
        flags.add(SASTFlag("tool3", "quicksort.c", 42, "vuln3"))  # Function "quickSort"

        expected = SASTFlags()
        expected.add(GroupedSASTFlag("tool1-tool3", "quicksort.c", (40 + 1), "vuln1:42-vuln3:42", 1, 7, 2, 3, 0.405))
        expected.add(GroupedSASTFlag("tool2", "quicksort.c", (13 + 1), "vuln2:27", 1, 11, 1, 3, 0.212))

        # Act
        actual = self.grouping.group(flags)

        # Assert
        self.assertEqual(unfold(expected), unfold(actual))

    def test_group_scope_func(self) -> None:
        # Arrange
        flags = SASTFlags()
        flags.add(SASTFlag("tool1", "quicksort.c", 54, "vuln1"))  # Outside of function(s)
        flags.add(SASTFlag("tool2", "quicksort.c", 60, "vuln2"))  # Function "printArray"
        flags.add(SASTFlag("tool3", "quicksort.c", 67, "vuln3"))  # Function "main"

        expected = SASTFlags()
        expected.add(GroupedSASTFlag("tool2", "quicksort.c", (56 + 1), "vuln2:60", 1, 6, 1, 3, 0.25))
        expected.add(GroupedSASTFlag("tool3", "quicksort.c", (65 + 1), "vuln3:67", 1, 8, 1, 3, 0.229))

        # Act
        actual = self.grouping.group(flags)

        # Assert
        self.assertEqual(unfold(expected), unfold(actual))

    def test_group_scope_file(self) -> None:
        # Arrange
        flags = SASTFlags()
        flags.add(SASTFlag("tool1", "main.c", 67, "vuln1"))  # Wrong file
        flags.add(SASTFlag("tool2", "quicksort.c", 60, "vuln2"))  # Function "printArray"
        flags.add(SASTFlag("tool3", "quicksort.c", 67, "vuln3"))  # Function "main"

        expected = SASTFlags()
        expected.add(GroupedSASTFlag("tool2", "quicksort.c", (56 + 1), "vuln2:60", 1, 6, 1, 3, 0.25))
        expected.add(GroupedSASTFlag("tool3", "quicksort.c", (65 + 1), "vuln3:67", 1, 8, 1, 3, 0.229))

        # Act
        actual = self.grouping.group(flags)

        # Assert
        self.assertEqual(unfold(expected), unfold(actual))


if __name__ == "__main__":
    unittest.main()
