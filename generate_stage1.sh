#! /bin/bash

for i in {1..200}; do
    python -u assign_teams_stage1.py $i | tee out_stage1/$i.txt
done
