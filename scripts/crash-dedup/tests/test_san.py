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

from cdd.container.san import (
    SanitizerOutput,
    StackFrame,
    frame_to_string,
    string_to_frame,
    trace_to_string,
    string_to_trace,
    STACK_FRAME_SEP,
    STACK_TRACE_SEP,
)


class TestStackFrame(unittest.TestCase):
    def test_frame_to_string(self) -> None:
        # Arrange
        frame = StackFrame(0, "/path/to/file", "func", 10)
        expected = f"#0{STACK_FRAME_SEP}/path/to/file{STACK_FRAME_SEP}func{STACK_FRAME_SEP}10"

        # Act
        actual = frame_to_string(frame)

        # Assert
        self.assertEqual(expected, actual)

    def test_string_to_frame(self) -> None:
        # Arrange
        frame = f"#0{STACK_FRAME_SEP}/path/to/file{STACK_FRAME_SEP}func{STACK_FRAME_SEP}10"
        expected = StackFrame(0, "/path/to/file", "func", 10)

        # Act
        actual = string_to_frame(frame)

        # Assert
        self.assertEqual(expected, actual)


class TestStackTrace(unittest.TestCase):
    def test_trace_to_string(self) -> None:
        # Arrange
        trace = [
            StackFrame(0, "/path/to/file01", "funcA", 10),
            StackFrame(1, "/path/to/file02", "funcB", 20),
            StackFrame(2, "/path/to/file03", "funcC", 30),
        ]
        expected = (
              f"#0{STACK_FRAME_SEP}/path/to/file01{STACK_FRAME_SEP}funcA{STACK_FRAME_SEP}10{STACK_TRACE_SEP}"
            + f"#1{STACK_FRAME_SEP}/path/to/file02{STACK_FRAME_SEP}funcB{STACK_FRAME_SEP}20{STACK_TRACE_SEP}"
            + f"#2{STACK_FRAME_SEP}/path/to/file03{STACK_FRAME_SEP}funcC{STACK_FRAME_SEP}30"
        )

        # Act
        actual = trace_to_string(trace)

        # Assert
        self.assertEqual(expected, actual)

    def test_string_to_trace(self) -> None:
        # Arrange
        trace = (
              f"#0{STACK_FRAME_SEP}/path/to/file01{STACK_FRAME_SEP}funcA{STACK_FRAME_SEP}10{STACK_TRACE_SEP}"
            + f"#1{STACK_FRAME_SEP}/path/to/file02{STACK_FRAME_SEP}funcB{STACK_FRAME_SEP}20{STACK_TRACE_SEP}"
            + f"#2{STACK_FRAME_SEP}/path/to/file03{STACK_FRAME_SEP}funcC{STACK_FRAME_SEP}30"
        )
        expected = [
            StackFrame(0, "/path/to/file01", "funcA", 10),
            StackFrame(1, "/path/to/file02", "funcB", 20),
            StackFrame(2, "/path/to/file03", "funcC", 30),
        ]

        # Act
        actual = string_to_trace(trace)

        # Assert
        self.assertEqual(expected, actual)


class TestSanitizerOutput(unittest.TestCase):
    def test_from_file(self) -> None:
        # Arrange
        sanitizer_files = [
            Path(__file__).parent / "data" / "sanitizer" / "test.703472",
            Path(__file__).parent / "data" / "sanitizer" / "test.703478",
            Path(__file__).parent / "data" / "sanitizer" / "test.703498",
            Path(__file__).parent / "data" / "sanitizer" / "test.703513",
            Path(__file__).parent / "data" / "sanitizer" / "test.703514",
            Path(__file__).parent / "data" / "sanitizer" / "test.703515",
        ]

        expected = [
            SanitizerOutput(
                "/path/to/file01",
                "addresssanitizer",
                "segv",
                [
                    StackFrame(0, "outputscript.c", "outputSWF_TEXT_RECORD", 1429),
                    StackFrame(1, "outputscript.c", "outputSWF_DEFINETEXT", 1471),
                    StackFrame(2, "outputscript.c", "outputBlock", 2079),
                    StackFrame(3, "main.c", "readMovie", 277),
                    StackFrame(4, "main.c", "main", 350),
                    StackFrame(5, "libc-start.c", "__libc_start_main", 308),
                    StackFrame(6, "-", "_start", -1),
                ],
            ),
            SanitizerOutput(
                "/path/to/file04",
                "addresssanitizer",
                "segv",
                [
                    StackFrame(0, "decompile.c", "OpCode", 868),
                    StackFrame(1, "decompile.c", "decompileINCR_DECR", 1474),
                    StackFrame(2, "decompile.c", "decompileAction", 3225),
                    StackFrame(3, "decompile.c", "decompileActions", 3401),
                    StackFrame(4, "decompile.c", "decompile5Action", 3423),
                    StackFrame(5, "outputscript.c", "outputSWF_DOACTION", 1548),
                    StackFrame(6, "outputscript.c", "outputBlock", 2079),
                    StackFrame(7, "main.c", "readMovie", 277),
                    StackFrame(8, "main.c", "main", 350),
                    StackFrame(9, "libc-start.c", "__libc_start_main", 308),
                    StackFrame(10, "-", "_start", -1),
                ],
            ),
            SanitizerOutput(
                "/path/to/file14",
                "addresssanitizer",
                "heap-buffer-overflow",
                [
                    StackFrame(0, "asan_interceptors.cpp", "strcat", 375),
                    StackFrame(1, "decompile.c", "dcputs", 104),
                    StackFrame(2, "decompile.c", "decompileIMPLEMENTS", 3094),
                    StackFrame(3, "decompile.c", "decompileAction", 3375),
                    StackFrame(4, "decompile.c", "decompileActions", 3401),
                    StackFrame(5, "decompile.c", "decompile5Action", 3423),
                    StackFrame(6, "outputscript.c", "outputSWF_DOACTION", 1548),
                    StackFrame(7, "outputscript.c", "outputBlock", 2079),
                    StackFrame(8, "main.c", "readMovie", 277),
                    StackFrame(9, "main.c", "main", 350),
                    StackFrame(10, "libc-start.c", "__libc_start_main", 308),
                    StackFrame(11, "-", "_start", -1),
                ],
            ),
            SanitizerOutput(
                "/path/to/file22",
                "addresssanitizer",
                "segv",
                [
                    StackFrame(0, "c2mir.c", "error", 856),
                    StackFrame(1, "c2mir.c", "get_header_name", 2967),
                    StackFrame(2, "c2mir.c", "process_directive", 3091),
                    StackFrame(3, "c2mir.c", "processing", 3569),
                    StackFrame(4, "c2mir.c", "pre", 3807),
                    StackFrame(5, "-", "-", -1),
                    StackFrame(6, "-", "-", -1),
                ],
            ),
            SanitizerOutput(
                "/path/to/file23",
                "leaksanitizer",
                "detected",
                [
                    StackFrame(0, "asan_malloc_linux.cpp", "realloc", 164),
                    StackFrame(1, "public.c", "defaultRealloc", 1092),
                ],
            ),
            SanitizerOutput("/path/to/file24", "addresssanitizer", "segv", []),
        ]

        # Act
        actual = [SanitizerOutput.from_file(f) for f in sanitizer_files]

        # Assert
        for i in range(len(expected)):
            self.assertEqual(expected[i], actual[i])
