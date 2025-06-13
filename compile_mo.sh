#!/bin/bash
# run with -i to drop a shell even if compile fails
# expects environment variable MCECS
BUILD_COMMAND="make"

# create random directory in /tmp/
RAND_DIR="/tmp/`dd if=/dev/urandom bs=1 count=6 status=none | base64`"
rsync -avhq --delete . $MCECS@mo.ece.pdx.edu:$RAND_DIR

ssh $MCECS@mo.ece.pdx.edu -t "zsh -l -c 'cd $RAND_DIR && $BUILD_COMMAND `[[ $1 == '-i' ]] && echo ";" || echo "&&"` zsh -i;rm -r $RAND_DIR'"
