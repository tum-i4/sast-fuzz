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

import shutil
from os import walk
from pathlib import Path
from typing import List, Optional, Set


def get_parent(path: Path, depth: int = 1) -> Path:
    """
    Return the n-th parent of a path.

    :param path:
    :param depth:
    :return:
    """
    if depth == 0:
        return path

    depth -= 1

    return get_parent(path.parent, depth)


def copy_dir(src_dir: Path, dst_dir: Path, overwrite: bool = True, extend_dst: bool = True) -> Optional[Path]:
    """
    Copy the contents of a source to a destination directory.

    :param src_dir: Source directory
    :param dst_dir: Destination directory
    :param overwrite: If true, overwrite existing files, otherwise, raise exception
    :param extend_dst: If true, extend dest. with source dir name, otherwise, no changes
    :return: Destination directory path if no exception occurred
    """
    if extend_dst:
        dst_dir = dst_dir / src_dir.name

    shutil.copytree(src_dir, dst_dir, dirs_exist_ok=overwrite)

    return dst_dir


def find_files(root_dir: Path, exts: Optional[List[str]] = None, rec: bool = True) -> Set[Path]:
    """
    Search for files in a directory.

    :param root_dir: Directory to start the search from
    :param exts: Allowed file extension
    :param rec: If true, perform recursive search, otherwise, only at top-level
    :return: Set of files
    """
    files: Set[Path] = set()

    for root, _, _files in walk(root_dir):
        files.update([Path(root) / Path(file) for file in _files if (exts is None or Path(file).suffix in exts)])

        if not rec:
            break

    return files
