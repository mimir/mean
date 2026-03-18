#!/bin/bash
set -eu

docker save mimir | gzip > mimir.tar.gz
