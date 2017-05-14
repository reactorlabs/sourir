#!/usr/bin/env bash
SOURIR="../sourir"

# Move into examples directory
pushd examples > /dev/null 2>&1

# Create a temp directory
TEMPDIR=`mktemp -d`

# Confirm that we created the directory
if [[ ! "$TEMPDIR" || ! -d "$TEMPDIR" ]]; then
  echo "Could not create temp dir!"
  exit 1
fi

# Always delete temp dir and its contents
function cleanup {
  rm -rf "$TEMPDIR"
  popd > /dev/null 2>&1
}
trap cleanup EXIT

# Test file $1
function runtest {
  echo "running test $1"
  yes 0 | $SOURIR "$1" --quiet --opt all > $TEMPDIR/$1.opt.out && \
  yes 0 | $SOURIR "$1" --quiet > $TEMPDIR/$1.out && \
  diff $TEMPDIR/$1.out $TEMPDIR/$1.opt.out > /dev/null && \
  yes 1 | $SOURIR "$1" --quiet --opt all > $TEMPDIR/$1.opt.out && \
  yes 1 | $SOURIR "$1" --quiet > $TEMPDIR/$1.out && \
  diff $TEMPDIR/$1.out $TEMPDIR/$1.opt.out > /dev/null
}

# Iterate over examples in directory
ALL_OK=0
for f in *.sou; do
  runtest $f
  if [[ $? -ne 0 ]]; then
    echo "Example $f failed!"
    ALL_OK=127
  fi
done

exit $ALL_OK
