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

from os import walk
from pathlib import Path
from typing import List, Optional, Set


def find_files(
    root_dirs: List[Path], exts: Optional[List[str]] = None, rec: bool = False, blacklist: Optional[List[str]] = None
) -> Set[Path]:
    """
    Search for files in various directories.

    :param root_dirs: List of directories to start the search from
    :param exts: Allowed file extension
    :param rec: If true, perform recursive search, otherwise, only at top-level
    :param blacklist: List of filenames to be excluded from the result
    :return: Set of files
    """

    def include(f: Path) -> bool:
        return (exts is None or f.suffix in exts) and (blacklist is None or not f.name in blacklist)

    files: Set[Path] = set()

    for root_dir in root_dirs:
        for root, _, _files in walk(root_dir):
            files.update([Path(root) / Path(file) for file in _files if include(Path(file))])

            if not rec:
                break

    return files
