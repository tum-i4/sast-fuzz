import unittest
from pathlib import Path
from typing import Set

from sfa.util.fs import find_files


class TestFSUtils(unittest.TestCase):
    def setUp(self) -> None:
        self.root_dir = Path("data") / "stubs"

    def test_find_files_non_rec1(self) -> None:
        # Arrange
        expected = {self.root_dir / "test.json"}

        # Act
        actual = find_files(self.root_dir, rec=False)

        # Assert
        self.assertEqual(expected, actual)

    def test_find_files_non_rec2(self) -> None:
        # Arrange
        expected: Set[Path] = set()

        # Act
        actual = find_files(self.root_dir, exts=[".pdf"], rec=False)

        # Assert
        self.assertEqual(expected, actual)

    def test_find_files_rec1(self) -> None:
        # Arrange
        expected = {self.root_dir / "dir" / "test.csv", self.root_dir / "test.json"}

        # Act
        actual = find_files(self.root_dir, rec=True)

        # Assert
        self.assertEqual(expected, actual)

    def test_find_files_rec2(self) -> None:
        # Arrange
        expected = {self.root_dir / "test.json"}

        # Act
        actual = find_files(self.root_dir, exts=[".pdf", ".json"], rec=True)

        # Assert
        self.assertEqual(expected, actual)

    def test_find_files_rec3(self) -> None:
        # Arrange
        expected = {self.root_dir / "dir" / "test.csv"}

        # Act
        actual = find_files(self.root_dir, exts=[".csv"], rec=True)

        # Assert
        self.assertEqual(expected, actual)

    def test_find_files_rec4(self) -> None:
        # Arrange
        expected: Set[Path] = set()

        # Act
        actual = find_files(self.root_dir, exts=[".pdf"], rec=True)

        # Assert
        self.assertEqual(expected, actual)


if __name__ == "__main__":
    unittest.main()