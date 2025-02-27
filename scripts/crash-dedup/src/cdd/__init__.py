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

from collections import namedtuple
from dataclasses import dataclass
from pathlib import Path

import yaml

InputConfig = namedtuple("InputConfig", ["blacklist"])

# Path of the default config file.
DEFAULT_CONFIG_FILE: Path = Path.cwd() / "config.yml"


@dataclass
class AppConfig:
    """
    Application configuration.
    """

    inputConfig: InputConfig

    @classmethod
    def from_yaml(cls, file: Path) -> "AppConfig":
        """
        Load configuration from YAML file.

        :param file:
        :return:
        """

        config = yaml.safe_load(file.read_text())

        return cls(inputConfig=InputConfig(config["input_files"]["blacklist"]))
