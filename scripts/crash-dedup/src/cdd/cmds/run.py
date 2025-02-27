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
from pathlib import Path
from typing import List, Optional

import typer
from typing_extensions import Annotated

from cdd import DEFAULT_CONFIG_FILE, AppConfig
from cdd.container.san import SanitizerOutput
from cdd.grouping import group_by
from cdd.utils.fs import find_files
from cdd.utils.proc import get_cpu_count, run_program_with_sanitizer, run_with_multiproc


def main(
    shell_command: Annotated[
        Optional[str],
        typer.Option(
            "--command",
            help="Shell command to run the sanitizer-instrumented program under test. Note: Use @@ as placeholder for input files (--input).",
        ),
    ] = None,
    input_dirs: Annotated[
        Optional[List[Path]],
        typer.Option(
            "--input",
            writable=False,
            exists=True,
            file_okay=False,
            dir_okay=True,
            resolve_path=True,
            help="Path to the directory(s) containing the input files for program execution.",
        ),
    ] = None,
    sanitizer_dirs: Annotated[
        Optional[List[Path]],
        typer.Option(
            "--sanitizer-dir",
            writable=False,
            exists=True,
            file_okay=False,
            dir_okay=True,
            resolve_path=True,
            help="Path to directory(s) with already existing sanitizer output files.",
        ),
    ] = None,
    output_dir: Annotated[
        Path,
        typer.Option(
            "--output",
            writable=True,
            exists=True,
            file_okay=False,
            dir_okay=True,
            resolve_path=True,
            help="Path to the output directory.",
        ),
    ] = Path.cwd(),
    n_frames_list: Annotated[
        Optional[List[int]],
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
    config_file: Annotated[
        Path,
        typer.Option(
            "--config",
            writable=False,
            exists=True,
            file_okay=True,
            dir_okay=False,
            resolve_path=True,
            help="Path to the YAML configuration file.",
        ),
    ] = DEFAULT_CONFIG_FILE,
    parallel: Annotated[
        bool, typer.Option("--parallel", is_flag=True, help="Run the deduplication in parallel.")
    ] = False,
) -> None:
    app_config = AppConfig.from_yaml(config_file)

    sanitizer_dirs = sanitizer_dirs or []

    if shell_command is not None:
        if input_dirs is None:
            raise typer.BadParameter("Input directory(s) are not specified.", param_hint="--input")

        sanitizer_dir = output_dir / "sanitizer"
        sanitizer_dir.mkdir(exist_ok=True)

        n_jobs = 1 if not parallel else (get_cpu_count() - 1)

        run_with_multiproc(
            run_program_with_sanitizer,
            [
                (shell_command, input_file, sanitizer_dir)
                for input_file in find_files(input_dirs, blacklist=app_config.inputConfig.blacklist)
            ],
            n_jobs,
        )

        sanitizer_dirs.append(sanitizer_dir)

    sanitizer_files = find_files(sanitizer_dirs)

    if len(sanitizer_files) == 0:
        logging.info("No sanitizer output files found.")
        exit(1)

    sanitizer_infos = []
    for sanitizer_file in sanitizer_files:
        try:
            sanitizer_infos.append(SanitizerOutput.from_file(sanitizer_file))

        except Exception as ex:
            logging.error(ex)

    for n_frames in set(n_frames_list or [None]):  # type: ignore
        summary_file = output_dir / f"summary{'' if n_frames is None else '_nf' + str(n_frames)}.csv"

        summary = group_by(sanitizer_infos, n_frames, consider_filepaths, consider_lines)
        summary.to_csv(summary_file)
