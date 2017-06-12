#!/usr/bin/env bash

LONG=$1

export SOURIR="../sourir"

function ncores {
  if [[ "$OSTYPE" == "darwin"* ]]; then
    echo `sysctl -n hw.ncpu || echo 2`
  else
    echo `nproc || echo 2`
  fi
}

export OPTS="prune\nprune_no_hoist\nhoist_osr\nconst_fold\nhoist_assign\nhoist_drop\nmin_live\ninline_small\ninline_med"
export INPUTS="0\n1\n3\nnil\ntrue\nfalse"

# Move into examples directory
pushd examples > /dev/null 2>&1

# Create a temp directory
export TEMPDIR=`mktemp -d`

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

export ALL_OPTS=$TEMPDIR/all_opts
PROCS=1
if [[ "$LONG" == "--long" ]]; then
  # Long test: generate all subsets of optimization passes
  p() { [ $# -eq 0 ] && echo || (shift; p "$@") | while read r ; do echo -e "$1,$r\n$r"; done }
  echo -e $OPTS | p `cat` | sort | uniq | sed 's/,$//' | tail -n +2 > $ALL_OPTS
  PROCS=`ncores`
else
  echo "all" > $ALL_OPTS
fi


# Test file $1
function runtest {
  TEST=$1
  INPUT=$2
  OPT=$3

  OUT="$TEMPDIR/$TEST-$INPUT"
  BASELINE_OUT="$OUT-base.out"
  OPT_OUT="$OUT-$opt.out"

  # echo "running test $1"

  if [ ! -f $BASELINE_OUT ]; then
    yes "$INPUT" | $SOURIR "$TEST" --quiet &> "$BASELINE_OUT"
    if [ $? -ne 0 ]; then
      echo -e "\n\nBaseline run failed on $TEST with input $INPUT\n"
      echo " ----- LOG ----------------------------------------"
      cat $BASELINE_OUT
      echo " --------------------------------------------------"
      exit 255
    fi
  fi

  yes "$INPUT" | $SOURIR "$TEST" --opt $OPT --quiet &> "$OPT_OUT"
  if [ $? -ne 0 ]; then
    echo -e "\n\nOpt run failed on $TEST with input $INPUT and opts $OPT\n"
    echo " ----- LOG ----------------------------------------"
    cat $OPT_OUT
    echo " --------------------------------------------------"
    exit 255
  fi

  diff $BASELINE_OUT $OPT_OUT > /dev/null

  if [ $? -ne 0 ]; then
    echo -e "\n\nOutput differs on $NAME with input $INPUT and opts $OPT\n"
    echo " ----- DIFF ---------------------------------------"
    diff $BASELINE_OUT $OPT_OUT
    echo " --------------------------------------------------"
    exit 255
  fi
}

function status {
  name=$1
  done=`wc -l < $STATUS`
  echo -ne "\e[0K\r[${done}/${NUM_TESTS}] ${name}                    "
}

function runtests {
  TEST=$0
  status "$TEST"
  for i in `echo -e $INPUTS`
  do
    while read opt
    do
      runtest $TEST $i $opt
    done
  done < $ALL_OPTS
  echo $TEST >> $STATUS
  status "$TEST"
}

export -f runtests runtest status

export NUM_TESTS=`find . -name '*.sou' | wc -l`
export STATUS="$TEMPDIR/status"
touch $STATUS

find . -name '*.sou' | xargs -n 1 -P $PROCS bash -c 'runtests $@'
RET=$?

echo

exit $RET
