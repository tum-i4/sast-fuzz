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
from collections import namedtuple
from pathlib import Path
from typing import Generator, Optional, Set, Union

# CSV separator
CSV_SEP: str = ","

# SAST flag
SASTFlag = namedtuple("SASTFlag", ["tool", "file", "line", "vuln"])

# Grouped SAST flag
GroupedSASTFlag = namedtuple(
    "GroupedSASTFlag",
    ["tool", "file", "line", "vuln", "n_flg_lines", "n_all_lines", "n_run_tools", "n_all_tools", "score"],
)

# SAST flag type
SASTFlagType = Union[SASTFlag, GroupedSASTFlag]


def div(a: Union[int, float], b: Union[int, float]) -> float:
    """
    Safe division of a by b.

    :param a: numerator
    :param b: denominator
    :return:
    """
    return 0 if b == 0 else (a / b)


class SASTFlags:
    """
    SAST flag container.
    """

    def __init__(self, flags: Optional[Set[SASTFlagType]] = None) -> None:
        self._flags = set() if flags is None else flags

    def add(self, flag: SASTFlagType) -> None:
        """
        Add a single SAST flag.
        :param flag:
        :return:
        """
        self._flags.add(flag)

    def update(self, *var_flags: "SASTFlags") -> None:
        """
        Add multiple SAST flags.

        :param var_flags:
        :return:
        """
        for flags in var_flags:
            self._flags.update(flags._flags)

    def remove(self, flag: SASTFlagType) -> None:
        """
        Remove a single SAST flag.

        :param flag:
        :return:
        """
        self._flags.remove(flag)

    def to_csv(self, file: Path) -> None:
        """
        Write SAST flags to a CSV file.

        :param file:
        :return:
        """
        with file.open("w+") as csv_file:
            for flag in self._flags:
                csv_file.write(CSV_SEP.join(map(str, flag)) + os.linesep)

    @classmethod
    def from_csv(cls, file: Path) -> "SASTFlags":
        """
        Read SAST flags from a CSV file.

        :param file:
        :return:
        """
        flags = SASTFlags()

        with file.open("r") as csv_file:
            for line in csv_file:
                vals = line.strip().split(CSV_SEP)

                if len(vals) == 4:  # Regular SAST flag
                    flags.add(SASTFlag(vals[0], vals[1], int(vals[2]), vals[3]))

                if len(vals) == 9:  # Grouped SAST flag
                    flags.add(
                        GroupedSASTFlag(
                            vals[0],
                            vals[1],
                            int(vals[2]),
                            vals[3],
                            int(vals[4]),
                            int(vals[5]),
                            int(vals[6]),
                            int(vals[7]),
                            float(vals[8]),
                        )
                    )

        return flags

    def __eq__(self, other: object) -> bool:
        return False if not isinstance(other, SASTFlags) else self._flags == other._flags

    def __iter__(self) -> Generator[SASTFlagType, None, None]:
        for flag in self._flags:
            yield flag

    def __len__(self) -> int:
        return len(self._flags)
