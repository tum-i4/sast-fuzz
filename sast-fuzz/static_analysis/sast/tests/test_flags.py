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

import os
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from sfa.analysis import CSV_SEP, SASTFlag, GroupedSASTFlag, SASTFlags


class TestFlags(unittest.TestCase):
    def setUp(self) -> None:
        self.flags = SASTFlags()
        self.flags.add(SASTFlag("tool1", "file1", 10, "vuln1"))
        self.flags.add(SASTFlag("tool2", "file2", 20, "vuln2"))

    def test_add(self) -> None:
        # Arrange
        flag = SASTFlag("tool3", "file3", 30, "vuln3")

        # Act
        self.flags.add(flag)

        # Assert
        self.assertIn(flag, self.flags)

    def test_update(self) -> None:
        # Arrange
        flag3 = SASTFlag("tool3", "file3", 30, "vuln3")
        flag4 = SASTFlag("tool4", "file4", 40, "vuln4")

        # Act
        self.flags.update(SASTFlags({flag3, flag4}))

        # Assert
        self.assertIn(flag3, self.flags)
        self.assertIn(flag4, self.flags)

        self.assertEqual(len(self.flags), 4)

    def test_update_multiple(self) -> None:
        # Arrange
        flag1 = SASTFlag("tool1", "file1", 10, "vuln1")
        flag2 = SASTFlag("tool2", "file2", 20, "vuln2")
        flag3 = SASTFlag("tool3", "file3", 30, "vuln3")
        flag4 = SASTFlag("tool4", "file4", 40, "vuln4")
        flag5 = SASTFlag("tool5", "file5", 50, "vuln5")
        flag6 = SASTFlag("tool6", "file6", 60, "vuln6")

        flags1 = SASTFlags({flag1, flag2})
        flags2 = SASTFlags({flag3, flag4})
        flags3 = SASTFlags({flag5, flag6})

        expected = SASTFlags({flag1, flag2, flag3, flag4, flag5, flag6})

        # Act
        flags1.update(flags2, flags3)

        actual = flags1

        # Assert
        self.assertEqual(expected, actual)

    def test_remove(self) -> None:
        # Arrange
        flag = SASTFlag("tool1", "file1", 10, "vuln1")

        # Act
        self.flags.remove(flag)

        # Assert
        self.assertNotIn(flag, self.flags)

    def test_to_csv(self) -> None:
        with TemporaryDirectory() as temp_dir:
            # Arrange
            temp_file = Path(temp_dir) / "file.csv"

            # Act
            self.flags.to_csv(temp_file)

            with temp_file.open("r") as file:
                lines = [line.strip() for line in file.readlines()]

            # Assert
            self.assertEqual(len(self.flags), len(lines))
            self.assertIn(CSV_SEP.join(["tool1", "file1", "10", "vuln1"]), lines)
            self.assertIn(CSV_SEP.join(["tool2", "file2", "20", "vuln2"]), lines)

    def test_from_csv(self) -> None:
        with TemporaryDirectory() as temp_dir:
            # Arrange
            temp_file = Path(temp_dir) / "test.csv"
            lines = [
                CSV_SEP.join(["tool1", "file1", "10", "vuln1"]) + os.linesep,
                CSV_SEP.join(["tool2", "file2", "20", "vuln2"]) + os.linesep,
                CSV_SEP.join(["tool3", "file3", "30", "vuln3"]) + os.linesep,
            ]

            with temp_file.open("w") as file:
                file.writelines(lines)

            # Act
            actual = SASTFlags.from_csv(temp_file)

            # Assert
            expected = SASTFlags()
            expected.add(SASTFlag("tool1", "file1", 10, "vuln1"))
            expected.add(SASTFlag("tool2", "file2", 20, "vuln2"))
            expected.add(SASTFlag("tool3", "file3", 30, "vuln3"))

            self.assertEqual(expected, actual)


class TestFlagsGrouped(unittest.TestCase):
    def setUp(self) -> None:
        self.flags = SASTFlags()
        self.flags.add(GroupedSASTFlag("tool1", "file1", 10, "vuln1", 1, 3, 1, 5, 0.267))
        self.flags.add(GroupedSASTFlag("tool2", "file2", 20, "vuln2", 1, 5, 1, 5, 0.200))

    def test_add(self) -> None:
        # Arrange
        flag = GroupedSASTFlag("tool3", "file3", 30, "vuln3", 1, 7, 1, 5, 0.171)

        # Act
        self.flags.add(flag)

        # Assert
        self.assertIn(flag, self.flags)

    def test_update(self) -> None:
        # Arrange
        flag3 = GroupedSASTFlag("tool3", "file3", 30, "vuln3", 1, 7, 1, 5, 0.171)
        flag4 = GroupedSASTFlag("tool4", "file4", 40, "vuln4", 1, 9, 1, 5, 0.156)

        # Act
        self.flags.update(SASTFlags({flag3, flag4}))

        # Assert
        self.assertIn(flag3, self.flags)
        self.assertIn(flag4, self.flags)

        self.assertEqual(len(self.flags), 4)

    def test_update_multiple(self) -> None:
        # Arrange
        flag1 = GroupedSASTFlag("tool1", "file1", 10, "vuln1", 1, 2, 1, 5, 0.350)
        flag2 = GroupedSASTFlag("tool2", "file2", 20, "vuln2", 1, 4, 1, 5, 0.225)
        flag3 = GroupedSASTFlag("tool3", "file3", 30, "vuln3", 1, 6, 1, 5, 0.183)
        flag4 = GroupedSASTFlag("tool4", "file4", 40, "vuln4", 1, 3, 1, 5, 0.267)
        flag5 = GroupedSASTFlag("tool5", "file5", 50, "vuln5", 1, 5, 1, 5, 0.200)
        flag6 = GroupedSASTFlag("tool6", "file6", 60, "vuln6", 1, 7, 1, 5, 0.171)

        flags1 = SASTFlags({flag1, flag2})
        flags2 = SASTFlags({flag3, flag4})
        flags3 = SASTFlags({flag5, flag6})

        expected = SASTFlags({flag1, flag2, flag3, flag4, flag5, flag6})

        # Act
        flags1.update(flags2, flags3)

        actual = flags1

        # Assert
        self.assertEqual(expected, actual)

    def test_remove(self) -> None:
        # Arrange
        flag = GroupedSASTFlag("tool1", "file1", 10, "vuln1", 1, 3, 1, 5, 0.267)

        # Act
        self.flags.remove(flag)

        # Assert
        self.assertNotIn(flag, self.flags)

    def test_to_csv(self) -> None:
        with TemporaryDirectory() as temp_dir:
            # Arrange
            temp_file = Path(temp_dir) / "file.csv"

            # Act
            self.flags.to_csv(temp_file)

            with temp_file.open("r") as file:
                lines = [line.strip() for line in file.readlines()]

            # Assert
            self.assertEqual(len(self.flags), len(lines))
            self.assertIn(CSV_SEP.join(["tool1", "file1", "10", "vuln1", "1", "3", "1", "5", "0.267"]), lines)
            self.assertIn(CSV_SEP.join(["tool2", "file2", "20", "vuln2", "1", "5", "1", "5", "0.2"]), lines)

    def test_from_csv(self) -> None:
        with TemporaryDirectory() as temp_dir:
            # Arrange
            temp_file = Path(temp_dir) / "test.csv"
            lines = [
                CSV_SEP.join(["tool1", "file1", "10", "vuln1", "1", "3", "1", "5", "0.267"]) + os.linesep,
                CSV_SEP.join(["tool2", "file2", "20", "vuln2", "1", "5", "1", "5", "0.200"]) + os.linesep,
                CSV_SEP.join(["tool3", "file3", "30", "vuln3", "1", "7", "1", "5", "0.171"]) + os.linesep,
            ]

            with temp_file.open("w") as file:
                file.writelines(lines)

            # Act
            actual = SASTFlags.from_csv(temp_file)

            # Assert
            expected = SASTFlags()
            expected.add(GroupedSASTFlag("tool1", "file1", 10, "vuln1", 1, 3, 1, 5, 0.267))
            expected.add(GroupedSASTFlag("tool2", "file2", 20, "vuln2", 1, 5, 1, 5, 0.200))
            expected.add(GroupedSASTFlag("tool3", "file3", 30, "vuln3", 1, 7, 1, 5, 0.171))

            self.assertEqual(expected, actual)


if __name__ == "__main__":
    unittest.main()
