#!/bin/bash
USER="$1"
[[ -z $USER ]] && USER=cogumbreiro
git push --mirror git@bitbucket.org:$USER/aniceto-coq.git
git push --mirror git@github.com:$USER/aniceto-coq.git
