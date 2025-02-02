#!/bin/sh -ex

PYTHON=${PYTHON:-python}

cd $(dirname $0)/npmjs

${PYTHON} prepare.py
npm install
npm run all

mkdir -p dist
npm pack --pack-destination dist