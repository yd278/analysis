#!/bin/bash
set -o pipefail # stop if any command fails

cd analysis/
lake exe cache get
lake build