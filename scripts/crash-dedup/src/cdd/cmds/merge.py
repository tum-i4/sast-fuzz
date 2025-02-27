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

import logging
from itertools import chain
from pathlib import Path
from typing import List, Optional

import typer
from typing_extensions import Annotated

from cdd.container.summary import DedupSummary
from cdd.grouping import group_by


def main(
    input_files: Annotated[
        List[Path],
        typer.Option(
            "--input",
            writable=False,
            exists=True,
            file_okay=True,
            dir_okay=False,
            resolve_path=True,
            help="Path to the input summary file.",
        ),
    ],
    output_file: Annotated[
        Path,
        typer.Option(
            "--output",
            writable=True,
            exists=False,
            file_okay=True,
            dir_okay=False,
            resolve_path=True,
            help="Path to the output summary file.",
        ),
    ],
    n_frames: Annotated[
        Optional[int],
        typer.Option(
            "--frames",
            min=1,
            help="Number(s) of stack frames to be included in the deduplication. Note: If not specified, all frames are considered.",
        ),
    ] = None,
    consider_filepaths: Annotated[
        bool,
        typer.Option(
            "--consider-filepaths",
            is_flag=True,
            help="Consider the file paths of the stack frames in the deduplication.",
        ),
    ] = False,
    consider_lines: Annotated[
        bool,
        typer.Option(
            "--consider-lines", is_flag=True, help="Consider the line numbers of the stack frames in the deduplication."
        ),
    ] = False,
) -> None:
    def flatten(l: List) -> List:
        return list(chain.from_iterable(l))

    try:
        sanitizer_infos = flatten(
            [entry.elems for entry in flatten([DedupSummary.from_csv(file).summary for file in input_files])]
        )

        summary = group_by(sanitizer_infos, n_frames, consider_filepaths, consider_lines)
        summary.to_csv(output_file)

    except Exception as ex:
        logging.error(ex)
        exit(1)
