# Antenna check of Magic on the whole cell.
load rcell
select top cell
extract do local
extract all
antennacheck debug
antennacheck
quit -noprompt
