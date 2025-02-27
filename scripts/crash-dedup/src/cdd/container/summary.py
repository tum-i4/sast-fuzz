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
from collections import defaultdict, namedtuple
from pathlib import Path
from typing import List, Optional, Tuple

from cdd.container.san import SanitizerOutput, StackTrace, string_to_trace, trace_to_string

# CSV separator
CSV_SEP: str = ","


DedupEntry = namedtuple("DedupEntry", ["bug_id", "key", "elems"])


class DedupSummary:
    """
    Deduplication summary container.
    """

    def __init__(
        self,
        n_frames: Optional[int],
        consider_filepaths: bool,
        consider_lines: bool,
        summary: Optional[List[DedupEntry]] = None,
    ) -> None:
        self.n_frames = n_frames
        self.consider_filepaths = consider_filepaths
        self.consider_lines = consider_lines
        self.summary = summary or []

    def add(self, id: int, key: Tuple, elems: List[SanitizerOutput]) -> None:
        self.summary.append(DedupEntry(id, key, elems))

    def to_csv(self, file: Path) -> None:
        """
        Write the deduplication summary to a CSV file.

        Args:
            file (Path): The file to write the summary to.
        """

        with file.open("w+") as csv_file:
            csv_file.write(
                CSV_SEP.join(
                    [
                        "bug_id",
                        "n_dedup_frames",
                        "consider_filepaths",
                        "consider_lines",
                        "input_file",
                        "sanitizer",
                        "vuln_type",
                        "stack_trace",
                        "n_total_frames",
                    ]
                )
                + os.linesep
            )

            for entry in self.summary:
                for san_output in entry.elems:
                    line = CSV_SEP.join(
                        (
                            str(entry.bug_id),
                            str(self.n_frames) if self.n_frames else "-",
                            str(self.consider_filepaths),
                            str(self.consider_lines),
                            str(san_output.input_file).replace(CSV_SEP, "-"),
                            san_output.sanitizer,
                            san_output.vuln_type,
                            trace_to_string(san_output.stack_trace),
                            str(len(san_output.stack_trace)),
                        )
                    )

                    csv_file.write(line + os.linesep)

    @classmethod
    def from_csv(cls, file: Path) -> "DedupSummary":
        """
        Read a deduplication summary from a CSV file.

        Args:
            file (Path): The file to read the summary from.

        Returns:
            DedupSummary: The deduplication summary.
        """

        def get_csv_entries(csv_line: str) -> Tuple[int, Optional[int], bool, bool, str, str, str, StackTrace, int]:
            values = csv_line.strip().split(CSV_SEP)
            return (
                int(values[0]),
                int(values[1]) if values[1] != "-" else None,
                True if values[2].lower() == "true" else False,
                True if values[3].lower() == "true" else False,
                values[4],
                values[5],
                values[6],
                string_to_trace(values[7]),
                int(values[8]),
            )

        with open(file, "r") as csv_file:
            lines = csv_file.readlines()

            _, n_dedup_frames, consider_filepaths, consider_lines, *_ = get_csv_entries(lines[1])

            dedup_dict = defaultdict(list)

            for line in lines[1:]:
                bug_id, _, _, _, input_file, sanitizer, vuln_type, stack_trace, _ = get_csv_entries(line)
                # Group sanitizer outputs by bug ID
                dedup_dict[bug_id].append(SanitizerOutput(input_file, sanitizer, vuln_type, stack_trace))

            dedup_list = [
                DedupEntry(bug_id, None, sanitizer_outputs) for bug_id, sanitizer_outputs in dedup_dict.items()
            ]

            return DedupSummary(n_dedup_frames, consider_filepaths, consider_lines, dedup_list)

    def __eq__(self, o: object) -> bool:
        if not isinstance(o, DedupSummary):
            return False

        return self.n_frames == o.n_frames and self.summary == o.summary
