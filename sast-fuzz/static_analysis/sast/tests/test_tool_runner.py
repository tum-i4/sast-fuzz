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
from sfa.analysis.tool_runner import convert_sarif


class TestFlagSetSarif(unittest.TestCase):
    def setUp(self) -> None:
        self.sarif_file = Path(__file__).parent / "data" / "test.sarif"

    def test_convert_sarif(self) -> None:
        # Arrange
        expected = SASTFlags()
        expected.add(SASTFlag("sast-tool", "file1", 10, "Rule-1"))
        expected.add(SASTFlag("sast-tool", "file2", 20, "Rule-2"))

        # Act
        actual = convert_sarif(self.sarif_file.read_text())

        # Assert
        self.assertEqual(expected, actual)


if __name__ == "__main__":
    unittest.main()
