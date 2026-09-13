"""Command-line entry point for lanky.

The real CLI will be assembled from ``Verb`` plugins (see :mod:`lanky.plugins`).
For this placeholder release ``main`` only reports what lanky is and where it lives.
"""

from __future__ import annotations

from lanky import __version__

REPO_URL = "https://github.com/xywei/lanky"


def main() -> int:
    """Print the name, version, status, and repository URL."""
    print("lanky")
    print(f"version: {__version__}")
    print("work in progress: placeholder release")
    print(REPO_URL)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
