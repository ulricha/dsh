#!/bin/bash

tab=${1}
file=${2}

query="
DropTable('${tab}', TRUE);
CreateTable('${tab}', ['p' slng, 'valr' dbl, 'vali' dbl]);
PrimaryKey('${tab}_pkey', '${tab}', ['p']);
SortKey('${tab}_skey', '${tab}', ['p']);
Append('${tab}',
       Project(AsciiLoad(['p', 'valr', 'vali'], '${file}', ',', '\n'),
               [p=slng(p), valr=dbl(valr), vali=dbl(vali)]));
Commit;
"

echo "${query}"
