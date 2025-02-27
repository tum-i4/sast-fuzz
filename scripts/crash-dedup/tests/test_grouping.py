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
from typing import Set

from cdd.container.san import SanitizerOutput, StackFrame
from cdd.container.summary import DedupSummary
from cdd.grouping import group_by


def check_grouping(summary: DedupSummary, expected: Set[str]) -> bool:
    """
    Check correctness of sanitizer output grouping.

    :param summary:
    :param expected:
    :return:
    """
    bug_id_map = {info.input_file: entry.bug_id for entry in summary.summary for info in entry.elems}

    bug_id = bug_id_map[list(expected)[0]]
    actual = set([s for s in bug_id_map.keys() if bug_id_map[s] == bug_id])

    return actual == expected


class TestGrouping(unittest.TestCase):
    def setUp(self) -> None:
        self.sanitizer_files = [
            Path(__file__).parent / "data" / "sanitizer" / "test.703472",
            Path(__file__).parent / "data" / "sanitizer" / "test.703480",
            Path(__file__).parent / "data" / "sanitizer" / "test.703482",
            Path(__file__).parent / "data" / "sanitizer" / "test.703486",
            Path(__file__).parent / "data" / "sanitizer" / "test.703498",
            Path(__file__).parent / "data" / "sanitizer" / "test.703500",
            Path(__file__).parent / "data" / "sanitizer" / "test.703504",
            Path(__file__).parent / "data" / "sanitizer" / "test.703506",
            Path(__file__).parent / "data" / "sanitizer" / "test.703510",
            Path(__file__).parent / "data" / "sanitizer" / "test.703512",
            Path(__file__).parent / "data" / "sanitizer" / "test.703514",
            Path(__file__).parent / "data" / "sanitizer" / "test.703515",
        ]

    def test_group_by_all_frames(self) -> None:
        # Arrange
        sanitizer_infos = [
            SanitizerOutput("input1", "san1", "type1", [StackFrame(1, "file1", "func1", 10)]),
            SanitizerOutput("input2", "san1", "type2", [StackFrame(2, "file2", "func2", 20)]),
            SanitizerOutput("input3", "san1", "type3", [StackFrame(3, "file3", "func3", 30)]),
        ]

        # Act
        actual = group_by(sanitizer_infos, None, True, True)

        # Assert
        n = len(actual.summary)
        for i in range(n):
            for j in range(n):
                if i != j:
                    bug_id_a = actual.summary[i].bug_id
                    bug_id_b = actual.summary[j].bug_id

                    self.assertNotEqual(bug_id_a, bug_id_b)

    def test_group_by_all_frames_same_vtype(self) -> None:
        # Arrange
        sanitizer_infos = [
            SanitizerOutput("input1", "san1", "type1", [StackFrame(1, "file1", "func1", 10)]),
            SanitizerOutput("input2", "san1", "type1", [StackFrame(2, "file2", "func2", 20)]),
            SanitizerOutput("input3", "san1", "type1", [StackFrame(3, "file3", "func3", 30)]),
        ]

        # Act
        actual = group_by(sanitizer_infos, None, True, True)

        # Assert
        n = len(actual.summary)
        for i in range(n):
            for j in range(n):
                if i != j:
                    bug_id_a = actual.summary[i].bug_id
                    bug_id_b = actual.summary[j].bug_id

                    self.assertNotEqual(bug_id_a, bug_id_b)

    def test_group_by_all_frames_same_trace(self) -> None:
        # Arrange
        sanitizer_infos = [
            SanitizerOutput("input1", "san1", "type1", [StackFrame(1, "file1", "func1", 10)]),
            SanitizerOutput("input2", "san1", "type2", [StackFrame(1, "file1", "func1", 10)]),
            SanitizerOutput("input3", "san1", "type3", [StackFrame(1, "file1", "func1", 10)]),
        ]

        # Act
        actual = group_by(sanitizer_infos, None, True, True)

        # Assert
        n = len(actual.summary)
        for i in range(n):
            for j in range(n):
                if i != j:
                    bug_id_a = actual.summary[i].bug_id
                    bug_id_b = actual.summary[j].bug_id

                    self.assertNotEqual(bug_id_a, bug_id_b)

    def test_group_by_all_frames_different_sanitizer(self) -> None:
        # Arrange
        sanitizer_infos = [
            SanitizerOutput("input1", "san1", "type1", [StackFrame(1, "file1", "func1", 10)]),
            SanitizerOutput("input2", "san2", "type1", [StackFrame(1, "file1", "func1", 10)]),
            SanitizerOutput("input3", "san3", "type1", [StackFrame(1, "file1", "func1", 10)]),
        ]

        # Act
        actual = group_by(sanitizer_infos, None, True, True)

        # Assert
        n = len(actual.summary)
        for i in range(n):
            for j in range(n):
                if i != j:
                    bug_id_a = actual.summary[i].bug_id
                    bug_id_b = actual.summary[j].bug_id

                    self.assertNotEqual(bug_id_a, bug_id_b)

    def test_group_by_all_frames_same_group(self) -> None:
        # Arrange
        sanitizer_infos = [
            SanitizerOutput("input1", "san1", "type1", [StackFrame(1, "file1", "func1", 10)]),
            SanitizerOutput("input2", "san1", "type1", [StackFrame(1, "file1", "func1", 10)]),
            SanitizerOutput("input3", "san1", "type1", [StackFrame(1, "file1", "func1", 10)]),
        ]

        # Act
        actual = group_by(sanitizer_infos, None, True, True)

        # Assert
        self.assertEqual(len(actual.summary), 1)

        for info in sanitizer_infos:
            self.assertIn(info, actual.summary[0].elems)

    def test_group_by_all_frames_same_group_ignore_filepaths(self) -> None:
        # Arrange
        sanitizer_infos = [
            SanitizerOutput("input1", "san1", "type1", [StackFrame(1, "file1", "func1", 10)]),
            SanitizerOutput("input2", "san1", "type1", [StackFrame(1, "file2", "func1", 10)]),
            SanitizerOutput("input3", "san1", "type1", [StackFrame(1, "file3", "func1", 10)]),
        ]

        # Act
        actual = group_by(sanitizer_infos, None, False, True)

        # Assert
        self.assertEqual(len(actual.summary), 1)

        for info in sanitizer_infos:
            self.assertIn(info, actual.summary[0].elems)

    def test_group_by_all_frames_same_group_ignore_lines(self) -> None:
        # Arrange
        sanitizer_infos = [
            SanitizerOutput("input1", "san1", "type1", [StackFrame(1, "file1", "func1", 10)]),
            SanitizerOutput("input2", "san1", "type1", [StackFrame(1, "file1", "func1", 20)]),
            SanitizerOutput("input3", "san1", "type1", [StackFrame(1, "file1", "func1", 30)]),
        ]

        # Act
        actual = group_by(sanitizer_infos, None, True, False)

        # Assert
        self.assertEqual(len(actual.summary), 1)

        for info in sanitizer_infos:
            self.assertIn(info, actual.summary[0].elems)

    def test_group_by_all_frames_same_group_ignore_filepaths_and_lines(self) -> None:
        # Arrange
        sanitizer_infos = [
            SanitizerOutput("input1", "san1", "type1", [StackFrame(1, "file1", "func1", 10)]),
            SanitizerOutput("input2", "san1", "type1", [StackFrame(1, "file2", "func1", 20)]),
            SanitizerOutput("input3", "san1", "type1", [StackFrame(1, "file3", "func1", 30)]),
        ]

        # Act
        actual = group_by(sanitizer_infos, None, False, False)

        # Assert
        self.assertEqual(len(actual.summary), 1)

        for info in sanitizer_infos:
            self.assertIn(info, actual.summary[0].elems)

    def test_group_by_all_frames_real_vulns(self) -> None:
        # Arrange
        sanitizer_infos = [SanitizerOutput.from_file(f) for f in self.sanitizer_files]

        expected = [
            {"/path/to/file01", "/path/to/file06"},
            {"/path/to/file05"},
            {"/path/to/file08", "/path/to/file15", "/path/to/file18", "/path/to/file21"},
            {"/path/to/file17"},
            {"/path/to/file14"},
            {"/path/to/file20"},
            {"/path/to/file23"},
            {"/path/to/file24"},
        ]

        # Act
        actual = group_by(sanitizer_infos, None, True, True)

        # Assert
        for group in expected:
            self.assertTrue(check_grouping(actual, group))

    def test_group_by_n_frames_1(self) -> None:
        # Arrange
        sanitizer_infos = [SanitizerOutput.from_file(f) for f in self.sanitizer_files]

        expected = [
            {"/path/to/file01", "/path/to/file06", "/path/to/file05"},
            {"/path/to/file08", "/path/to/file15", "/path/to/file18", "/path/to/file21"},
            {"/path/to/file17"},
            {"/path/to/file14", "/path/to/file20"},
            {"/path/to/file23"},
            {"/path/to/file24"},
        ]

        # Act
        actual = group_by(sanitizer_infos, 1, True, True)

        # Assert
        for group in expected:
            self.assertTrue(check_grouping(actual, group))

    def test_group_by_n_frames_5(self) -> None:
        # Arrange
        sanitizer_infos = [SanitizerOutput.from_file(f) for f in self.sanitizer_files]

        expected = [
            {"/path/to/file01", "/path/to/file06"},
            {"/path/to/file05"},
            {"/path/to/file08", "/path/to/file15", "/path/to/file18", "/path/to/file21"},
            {"/path/to/file17"},
            {"/path/to/file14", "/path/to/file20"},
            {"/path/to/file23"},
            {"/path/to/file24"},
        ]

        # Act
        actual = group_by(sanitizer_infos, 5, True, True)

        # Assert
        for group in expected:
            self.assertTrue(check_grouping(actual, group))

    def test_group_by_n_frames_7(self) -> None:
        # Arrange
        sanitizer_infos = [SanitizerOutput.from_file(f) for f in self.sanitizer_files]

        expected = [
            {"/path/to/file01", "/path/to/file06"},
            {"/path/to/file05"},
            {"/path/to/file08", "/path/to/file15", "/path/to/file18", "/path/to/file21"},
            {"/path/to/file17"},
            {"/path/to/file14"},
            {"/path/to/file20"},
            {"/path/to/file23"},
            {"/path/to/file24"},
        ]

        # Act
        actual = group_by(sanitizer_infos, 7, True, True)

        # Assert
        for group in expected:
            self.assertTrue(check_grouping(actual, group))
