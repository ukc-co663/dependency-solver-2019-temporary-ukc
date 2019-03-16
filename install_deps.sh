#!/bin/bash
apt-get update
apt-get install -y python3-pip
python3 -m pip install z3-solver packaging
