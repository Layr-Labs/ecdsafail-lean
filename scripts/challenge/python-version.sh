# Source before any build or artifact work. Use the same interpreter for the
# challenge checks and the pinned source replay called by the full verifier.
challenge_python="${ECDSA_SOURCE_PYTHON:-python3}"
"$challenge_python" -c 'import sys
if sys.version_info < (3, 10):
    sys.exit("Python >=3.10 is required; set ECDSA_SOURCE_PYTHON to a supported interpreter")'
export ECDSA_SOURCE_PYTHON="$challenge_python"
