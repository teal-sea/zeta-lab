"""The package metadata and quickstart must survive a standalone Hub pull."""
from pathlib import Path
import tomllib

ROOT = Path(__file__).resolve().parents[1]


def test_every_direct_runtime_import_is_declared():
    project = tomllib.loads((ROOT / "pyproject.toml").read_text())["project"]
    dependencies = project["dependencies"]
    assert any(item.startswith("datasets==") for item in dependencies)


def test_sdist_include_names_only_files_prime_preserves():
    config = tomllib.loads((ROOT / "pyproject.toml").read_text())
    included = set(config["tool"]["hatch"]["build"]["targets"]["sdist"]["include"])
    assert included == {"bloch_certificate", "tests", "README.md", "pyproject.toml"}


def test_quickstart_works_from_a_standalone_package_root():
    readme = (ROOT / "README.md").read_text()
    assert "pip install -e ." in readme
    assert "--env-dir-path environments" not in readme
    assert "prime env install thomas-lince/bloch-certificate@latest" in readme
