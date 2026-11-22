i want to support gnark backend. that is, write the front end circuit in xark; this will produce an xark format r1cs circuit. convert this circuit to gnark readable format. 

the e2e of this procedure should be that the user can simply write xark circuit and prove with gnark backend. the gnark backend can be optional, as an alternative to arkworks. 

for second pahse
it should also come up with some simple benchmark:
for a same function, such as fibonacci or poseidon2, what are the r1cs number of constraits writte in xark and in gnark. eventually i am expecting a table

rows are
- xark + arkwroks 
- xark + gnark
- pure gnark

for both poseidon2 and fibonacci; for each application, i need both r1cs count and proving time, as the columns.