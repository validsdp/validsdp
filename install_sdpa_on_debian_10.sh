#!/bin/bash

# This script is intended to workaround the following issue:
#
# Package sdpa is missing in the Debian APT archive(s) buster;
# see: https://packages.debian.org/bullseye/sdpa
# and: https://packages.debian.org/sid/sdpa
#
# Beware: this script may break your Debian distribution; use it with
# caution! - all the more as SDPA is an optional ValidSDP dependency.

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
