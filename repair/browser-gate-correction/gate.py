#!/usr/bin/env python3
import sys
from gate_core import gate_file


def main():
    if len(sys.argv) != 2:
        sys.stderr.write("usage: python3 gate.py FILE.jdg\n")
        return 2
    code, text = gate_file(sys.argv[1])
    sys.stdout.write(text)
    return code


if __name__ == "__main__":
    raise SystemExit(main())
