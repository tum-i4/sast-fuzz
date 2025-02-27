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
import sys
from pathlib import Path
from typing import List, Optional

import typer
from typing_extensions import Annotated

from sfa import AppConfig
from sfa.analysis import SASTFlags
from sfa.analysis.factory import (
    SASTFlagFilterFactory,
    SASTFlagFilterMode,
    SASTFlagGroupingFactory,
    SASTFlagGroupingMode,
    SASTTool,
    SASTToolRunnerFactory,
)
from sfa.analysis.tool_runner import BUILD_SCRIPT_NAME, SASTToolRunner
from sfa.utils.proc import run_with_multiproc

logging.basicConfig(format="%(asctime)s SFA[%(levelname)s]: %(message)s", level=logging.INFO, stream=sys.stdout)

# Path of the default config file.
DEFAULT_CONFIG_FILE = Path.cwd() / "config.yml"

# Path of the default output file.
DEFAULT_OUTPUT_FILE = Path.cwd() / "output.csv"

app = typer.Typer()


def _starter(runner: SASTToolRunner) -> SASTFlags:
    return runner.run()


def run_tools(
    flags: SASTFlags, tools: List[SASTTool], subject_dir: Path, app_config: AppConfig, parallel: bool
) -> SASTFlags:
    """
    Run SAST tools.

    :param flags:
    :param tools:
    :param subject_dir:
    :param app_config:
    :param parallel:
    :return:
    """
    logging.info(f"SAST tools: {', '.join([t.value for t in tools])}")

    n_jobs = 1 if not parallel else len(tools)
    tool_runners = [(runner,) for runner in SASTToolRunnerFactory((subject_dir, app_config)).get_instances(tools)]

    nested_flags = run_with_multiproc(_starter, tool_runners, n_jobs)

    flags.update(*map(SASTFlags, nested_flags))

    return flags


def filter_flags(flags: SASTFlags, filter_modes: List[SASTFlagFilterMode], inspec_file: Path) -> SASTFlags:
    """
    Filter SAST flags.

    :param flags:
    :param filter_modes:
    :param inspec_file:
    :return:
    """
    for flag_filter in SASTFlagFilterFactory(inspec_file).get_instances(filter_modes):
        flags = flag_filter.filter(flags)

    return flags


def group_flags(
    flags: SASTFlags, grouping_mode: SASTFlagGroupingMode, inspec_file: Path, app_config: AppConfig
) -> SASTFlags:
    """
    Group SAST flags.

    :param flags:
    :param grouping_mode:
    :param inspec_file:
    :return:
    """
    flag_grouping = SASTFlagGroupingFactory((inspec_file, app_config)).get_instance(grouping_mode)

    return flag_grouping.group(flags)


@app.command()
def main(
    flag_files: Annotated[
        Optional[List[Path]],
        typer.Option(
            "--flags",
            writable=False,
            exists=True,
            file_okay=True,
            dir_okay=False,
            resolve_path=True,
            help="Path to the file(s) containing SAST tool flags.",
        ),
    ] = None,
    subject_dir: Annotated[
        Optional[Path],
        typer.Option(
            "--subject",
            writable=True,
            exists=True,
            file_okay=False,
            dir_okay=True,
            resolve_path=True,
            help="Path to the root directory of the target program.",
        ),
    ] = None,
    inspec_file: Annotated[
        Optional[Path],
        typer.Option(
            "--inspection",
            writable=False,
            exists=True,
            file_okay=True,
            dir_okay=False,
            resolve_path=True,
            help="Path to the SASTFuzz Inspector (SFI) file.",
        ),
    ] = None,
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
    output_file: Annotated[
        Path,
        typer.Option(
            "--output",
            writable=True,
            exists=False,
            file_okay=True,
            dir_okay=False,
            resolve_path=True,
            help="Path to the CSV output file.",
        ),
    ] = DEFAULT_OUTPUT_FILE,
    tools: Annotated[
        Optional[List[SASTTool]],
        typer.Option(
            "--tool",
            help="SAST tool(s) to be used for the analysis. Note: To run the tools, the subject directory must be specified (--subject).",
        ),
    ] = None,
    parallel: Annotated[bool, typer.Option("--parallel", is_flag=True, help="Run the SAST tools in parallel.")] = False,
    filter_modes: Annotated[
        Optional[List[SASTFlagFilterMode]],
        typer.Option(
            "--filter",
            help="Filter(s) to be applied on the SAST flags. Note: To apply the filters, the SFI file must be specified (--inspection).",
        ),
    ] = None,
    grouping_mode: Annotated[
        Optional[SASTFlagGroupingMode],
        typer.Option(
            "--grouping",
            help="Grouping to be applied on the SAST flags. Note: To apply the grouping, the SFI file must be specified (--inspection).",
        ),
    ] = None,
) -> None:
    if tools:
        if subject_dir is None:
            raise typer.BadParameter("Subject directory is not specified.", param_hint="--subject")

        if not (subject_dir / BUILD_SCRIPT_NAME).exists():
            raise typer.BadParameter("Build script couldn't be found in the subject directory.", param_hint="--subject")

    if filter_modes or grouping_mode:
        if inspec_file is None:
            raise typer.BadParameter("SASTFuzz Inspector file is not specified.", param_hint="--inspection")

    app_config = AppConfig.from_yaml(config_file)

    flags = SASTFlags()
    flags.update(*map(SASTFlags.from_csv, flag_files or []))

    if tools:
        flags = run_tools(flags, tools, subject_dir, app_config, parallel)  # type: ignore
    if filter_modes:
        flags = filter_flags(flags, filter_modes, inspec_file)  # type: ignore
    if grouping_mode:
        flags = group_flags(flags, grouping_mode, inspec_file, app_config)  # type: ignore

    flags.to_csv(output_file)
