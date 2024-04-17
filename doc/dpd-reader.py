import csv
import re

def parse_and_generate_csv(input_filename, nodes_csv_filename, edges_csv_filename):
    with \
        open(input_filename, "r") as input_file,\
        open(nodes_csv_filename, "w", newline="") as nodes_csv,\
        open(edges_csv_filename, "w", newline="") as edges_csv:
        input_text = input_file.read()
        nodes_writer = csv.writer(nodes_csv)
        edges_writer = csv.writer(edges_csv)

        nodes_writer.writerow(["id", "name", "body", "kind", "prop", "path"])
        edges_writer.writerow(["source", "target", "weight"])

        node_data = {}
        for line in input_text.strip().split("\n"):
            if line.startswith("N:"):
                match = re.match(r'N:\s+(\d+)\s+"([^"]+)"\s+\[([^\]]+)\]\s*;', line)
                if match:
                    node_id, node_name, node_attributes = match.group(1), match.group(2), match.group(3)
                    attributes = dict(re.findall(r'(\w+)="?(\w+)"?', node_attributes))
                    node_data[node_id] = {"name": node_name, **attributes}
                    data = node_data[node_id]
                    nodes_writer.writerow([
                        node_id,
                        data["name"],
                        data.get("body", ""),
                        data.get("kind", ""),
                        data.get("prop", ""),
                        data.get("path", "")
                    ])

            elif line.startswith("E:"):
                match = re.match(r'E:\s+(\d+)\s+(\d+)\s+\[([^\]]+)\]\s*;', line)
                if match:
                    source_id, target_id, edge_attributes = match.group(1), match.group(2), match.group(3)
                    attributes = dict(re.findall(r'(\w+)=(\w+)', edge_attributes))
                    edges_writer.writerow([source_id, target_id, attributes.get("weight", "")])

# Example usage
parse_and_generate_csv("_build/default/catala.dpd", "data/nodes.csv", "data/edges.csv")


import csv
import networkx as nx

def load_csv_to_networkx(nodes_csv_filename, edges_csv_filename):
    G = nx.DiGraph()

    id_to_fullname = {}

    with open(nodes_csv_filename, "r") as nodes_csv:
        nodes_reader = csv.reader(nodes_csv)
        next(nodes_reader)  # Skip the header
        for row in nodes_reader:
            node_id, name, body, kind, prop, path = row
            id_to_fullname[node_id]  = path + "." + name
            G.add_node(id_to_fullname[node_id], name=name, body=body, kind=kind, prop=prop, path=path)

    with open(edges_csv_filename, "r") as edges_csv:
        edges_reader = csv.reader(edges_csv)
        next(edges_reader)  # Skip the header
        for row in edges_reader:
            source, target, weight = row
            G.add_edge(id_to_fullname[source], id_to_fullname[target], weight=weight)

    return G.reverse()

graph = load_csv_to_networkx("data/nodes.csv", "data/edges.csv")


u = set()
name_to_id = {v: k for k, v in dict(graph.nodes(data="name")).items()}

print(sorted(graph[name_to_id["append_stack"]].items(), key=lambda x: int(x[1]["weight"]), reverse=True))
