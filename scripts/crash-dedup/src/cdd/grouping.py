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

from itertools import groupby
from typing import List, Optional

from cdd.container.san import SanitizerOutput
from cdd.container.summary import DedupEntry, DedupSummary


def group_by(
    sanitizer_infos: List[SanitizerOutput],
    n_frames: Optional[int] = None,
    consider_filepaths: bool = False,
    consider_lines: bool = False,
) -> DedupSummary:
    """
    Group/deduplicate sanitizer outputs.

    :param sanitizer_infos:
    :param n_frames:
    :param consider_filepaths:
    :param consider_lines:
    :return:
    """
    keyfunc = lambda s: s.sorting_key(n_frames, consider_filepaths, consider_lines)

    return DedupSummary(
        n_frames,
        consider_filepaths,
        consider_lines,
        [
            DedupEntry(i, k, list(g))
            for i, (k, g) in enumerate(groupby(sorted(sanitizer_infos, key=keyfunc), key=keyfunc))
        ],
    )
