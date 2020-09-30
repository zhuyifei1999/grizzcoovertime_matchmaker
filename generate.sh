#! /bin/bash

for i in {1..200}; do
    python -u assign_teams.py $i | tee out/$i.txt
done
