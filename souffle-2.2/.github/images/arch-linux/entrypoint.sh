#!/bin/bash

set -e
set -x

envsubst '${RELEASE_TAG}' < PKGBUILD.in  > PKGBUILD
makepkg
makepkg --printsrcinfo > .SRCINFO
