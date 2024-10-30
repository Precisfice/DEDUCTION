.PHONY: hasse hasse2 hasse3

hasse: hasse2 hasse3

hasse2:
	dot -Tps  HasseD2.dot -o hasse2.ps
	dot -Tsvg HasseD2.dot -o hasse2.svg
	dot -Tpng HasseD2.dot -o hasse2.png

hasse3:
	dot -Tps  HasseD3.dot -o hasse3.ps
	dot -Tpng HasseD3.dot -o hasse3.png
