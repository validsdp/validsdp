#!/bin/bash

# This script is intended to fix the following issue:
#
# Package sdpa is missing in the Debian APT archives buster, bullseye;
# see also: https://packages.debian.org/sid/sdpa

set -ex

sudo tee /etc/apt/sources.list.d/sid.list \
     <<<"deb http://deb.debian.org/debian sid main"

sudo tee /etc/apt/preferences.d/00sid-pin <<EOF
Package: *
Pin: release n=sid
Pin-Priority: 100
EOF

sudo apt-get update -y -q

sudo DEBIAN_FRONTEND=noninteractive apt-get install -y -q -t sid --no-install-recommends sdpa

: sdpa installed
