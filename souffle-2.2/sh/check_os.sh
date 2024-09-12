#!/bin/bash

if [ -f "/etc/os-release" ]; then
    file="/etc/os-release"
elif [ -f "/usr/lib/os-release" ]; then
    file="/usr/lib/os-release"
else 
    exit 1
fi

grep -G "^ID=" $file | tr a-z A-Z
