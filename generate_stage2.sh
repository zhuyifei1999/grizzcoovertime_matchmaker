#! /bin/bash

for i in {1..200}; do
    python -u assign_teams_stage2.py $i | tee out_stage2/$i.txt
done
