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

from cdd.container.san import SanitizerOutput, StackFrame
from cdd.container.summary import DedupEntry, DedupSummary


class TestSummary(unittest.TestCase):
    def setUp(self):
        self.summary_file = Path(__file__).parent / "data" / "summary.csv"

    def test_from_csv(self) -> None:
        # Arrange
        expected = DedupSummary(
            n_frames=5,
            consider_filepaths=False,
            consider_lines=False,
            summary=[
                DedupEntry(
                    bug_id=0,
                    key=None,
                    elems=[
                        SanitizerOutput(
                            input_file="/path/to/file01",
                            sanitizer="addresssanitizer",
                            vuln_type="segv",
                            stack_trace=[
                                StackFrame(id=0, file="outputscript.c", function="outputSWF_TEXT_RECORD", line=1429),
                                StackFrame(id=1, file="outputscript.c", function="outputSWF_DEFINETEXT", line=1471),
                                StackFrame(id=2, file="outputscript.c", function="outputBlock", line=2079),
                                StackFrame(id=3, file="main.c", function="readMovie", line=277),
                                StackFrame(id=4, file="main.c", function="main", line=350),
                            ],
                        ),
                        SanitizerOutput(
                            input_file="/path/to/file03",
                            sanitizer="addresssanitizer",
                            vuln_type="segv",
                            stack_trace=[
                                StackFrame(id=0, file="outputscript.c", function="outputSWF_TEXT_RECORD", line=1429),
                                StackFrame(id=1, file="outputscript.c", function="outputSWF_DEFINETEXT", line=1471),
                                StackFrame(id=2, file="outputscript.c", function="outputBlock", line=2079),
                                StackFrame(id=3, file="main.c", function="readMovie", line=277),
                                StackFrame(id=4, file="main.c", function="main", line=350),
                            ],
                        ),
                    ],
                ),
                DedupEntry(
                    bug_id=1,
                    key=None,
                    elems=[
                        SanitizerOutput(
                            input_file="/path/to/file02",
                            sanitizer="addresssanitizer",
                            vuln_type="segv",
                            stack_trace=[
                                StackFrame(id=0, file="decompile.c", function="OpCode", line=868),
                                StackFrame(id=1, file="decompile.c", function="decompileINCR_DECR", line=1474),
                                StackFrame(id=2, file="decompile.c", function="decompileAction", line=3225),
                                StackFrame(id=3, file="decompile.c", function="decompileActions", line=3401),
                                StackFrame(id=4, file="decompile.c", function="decompile5Action", line=3423),
                                StackFrame(id=5, file="outputscript.c", function="outputSWF_DOACTION", line=1548),
                                StackFrame(id=6, file="outputscript.c", function="outputBlock", line=2079),
                                StackFrame(id=7, file="main.c", function="readMovie", line=277),
                                StackFrame(id=8, file="main.c", function="main", line=350),
                            ],
                        )
                    ],
                ),
                DedupEntry(
                    bug_id=2,
                    key=None,
                    elems=[
                        SanitizerOutput(
                            input_file="/path/to/file04",
                            sanitizer="addresssanitizer",
                            vuln_type="segv",
                            stack_trace=[
                                StackFrame(id=0, file="-", function="-", line=-1),
                                StackFrame(id=1, file="-", function="-", line=-1),
                                StackFrame(id=2, file="-", function="-", line=-1),
                            ],
                        )
                    ],
                ),
            ],
        )

        # Act
        actual = DedupSummary.from_csv(self.summary_file)

        # Assert
        self.assertEqual(expected, actual)
