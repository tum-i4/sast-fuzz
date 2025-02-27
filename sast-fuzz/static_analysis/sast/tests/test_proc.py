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

import unittest

from sfa.utils.proc import run_shell_command, run_with_multiproc


def square(x: int) -> int:
    """
    Square a number.

    :param x:
    :return:
    """
    return x**2


class TestProcUtils(unittest.TestCase):
    def test_run_shell_command(self) -> None:
        # Arrange
        cmd = "echo 'Hello, World!'"
        expected = "Hello, World!\n"

        # Act
        actual = run_shell_command(cmd)

        # Assert
        self.assertEqual(expected, actual)

    def test_run_with_multiproc(self) -> None:
        # Arrange

        vals = [(1,), (2,), (3,), (4,), (5,)]
        expected = [1, 4, 9, 16, 25]

        # Act
        actual = run_with_multiproc(square, vals, n_jobs=3)

        # Assert
        self.assertEqual(expected, actual)


if __name__ == "__main__":
    unittest.main()
