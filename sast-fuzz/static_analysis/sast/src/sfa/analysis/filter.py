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

import json
from abc import ABC, abstractmethod
from collections import defaultdict
from functools import lru_cache
from pathlib import Path
from typing import Dict, List

from sfa.analysis import SASTFlags


class SASTFlagFilter(ABC):
    """
    Abstract SAST flag filter.
    """

    def __init__(self, inspec_file: Path) -> None:
        self._inspec_file = inspec_file

    @abstractmethod
    def filter(self, flags: SASTFlags) -> SASTFlags:
        """
        Filter out certain SAST flags.

        :param flags:
        :return:
        """
        pass


class ReachabilityFilter(SASTFlagFilter):
    """
    SAST flag reachability filter.
    """

    def __init__(self, inspec_file: Path) -> None:
        super().__init__(inspec_file)
        self._reachable_code: Dict[str, List[Dict]] = defaultdict(list)

        data = json.loads(inspec_file.read_text())

        for func in data["functions"]:
            if func["location"]["reachable_from_main"]:
                self._reachable_code[func["location"]["filename"]].append(func["location"]["line"])

    @lru_cache(maxsize=None)
    def _is_reachable(self, file: str, line: int) -> bool:
        """
        Check if a code location is reachable from the main function.

        :param file:
        :param line:
        :return:
        """
        if file in self._reachable_code.keys():
            for line_range in self._reachable_code[file]:
                if line_range["start"] <= line <= line_range["end"]:
                    return True

        return False

    def filter(self, flags: SASTFlags) -> SASTFlags:
        """
        Filter out SAST flags unreachable from the main function.

        :param flags:
        :return:
        """
        return SASTFlags(set(filter(lambda flag: self._is_reachable(flag.file, flag.line), flags)))
