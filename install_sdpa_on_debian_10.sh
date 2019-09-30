#!/bin/bash

# This script is intended to fix the following issue:
#
# The sdpa package is missing in the Debian *buster* APT archive;
# see also: https://packages.debian.org/bullseye/sdpa

set -ex

sudo tee /etc/apt/sources.list.d/bullseye.list \
     <<<"deb http://deb.debian.org/debian bullseye main"

sudo tee /etc/apt/preferences.d/00bullseye-pin <<EOF
Package: *
Pin: release a=testing
Pin-Priority: 100
EOF

sudo apt-get update -y -q

sudo DEBIAN_FRONTEND=noninteractive apt-get install -y -q -t bullseye --no-install-recommends sdpa

: sdpa installed
