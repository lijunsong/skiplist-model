function get_text(filename) {
    var txt = '';
    var xmlhttp = new XMLHttpRequest();
    xmlhttp.onreadystatechange = function(){
      if(xmlhttp.status == 200 && xmlhttp.readyState == 4){
        txt = xmlhttp.responseText;
      }
    };
    xmlhttp.open("GET",filename,false);
    xmlhttp.send();
    return txt;
}


function parse_line(line) {
	if (line.indexOf("skolem") != -1 ||
		line.indexOf("=") == -1)
		return null;

	var c = line.split('=');
	var id = c[0].trim();
	var values = c[1].replace(/{|}| /g, "").split(",");
	return {"id": id, "value": values};

}

function parse_lines(lines) {
	var env = {}
	lines.forEach(function (line) {
		var obj = parse_line(line);
		if (obj == null)
			return;
		env[obj.id] = obj.value;
	});
	// revise time ordering
	var time = env["this/Time"];
	time.sort(function(t1,t2) {
		var t1_num = +(t1.match(/Time\$(\d+)/, t1)[1]);
		var t2_num = +(t2.match(/Time\$(\d+)/, t2)[1]);
		return t1_num - t2_num;
	});
	return env;
}

function get_env(filename) {
	var contents = get_text("data.txt");
	if (contents == '') {
		return null;
	}
	var lines = contents.split('\n');
	var env = parse_lines(lines);
	return env;
}

function get_relations_at_time(env, id, t) {
	var rs = env[id];
	var lst = [];
	rs.forEach(function (r) {
		if (r.indexOf(t) == -1)
			return;

		var new_r = r.replace("->"+t, '');
		lst.push(new_r);
	});
	return lst;
}

function get_new_id() {
	get_new_id.count = ++get_new_id.count || 0;
	return get_new_id.count;
}
function build_nodes_links_groups(env, t) {
	var result = {'nodes' : null, 'links': null};
	var links = [];
	var nodes = [];
	var groups = [];
	var lst = get_relations_at_time(env, 'this/Node<:succs', t);
	var succs = []; // succs contains [[node0,0,node1]...] tuples
	var level0 = {};
	get_new_id.count = -1; // the count should be starting from 0

	var get_node = function (level, groupname) {
		//given name, level and groupname, search if the node exist before
		// if it is not, return a new one, and add the new one to nodes
		var i = 0;
		for(i = 0; i < nodes.length; i++) {
			if (nodes[i].level == level && nodes[i].groupname == groupname) {
				return nodes[i];
			}
		}
		var n = {'name':get_new_id(), 'level':+level,'groupname': groupname};
		nodes.push(n);
		return n;
	}
	lst.forEach(function (l) {
		var r = l.split('->');
		// collect level0's info for building groups
		if (r[1] == '0') {
			level0[r[0]] = r[2];
		}
		// for r[0] and r[2] generate node for it
		var source = get_node(+r[1], r[0]);
		var target = get_node(+r[1], r[2]);
		//var link = { 'source' : source, 'target' : target};
		var link = {'source' : source.name, 'target' : target.name};

		links.push(link);
		succs.push(r);
	});

	// build the group info
	var inGroupSet = {};
	var nextNode = 'HeadNode$0';
	var visited = {}
	do {
		visited[nextNode] = 1;
		if (inGroupSet[nextNode] == null) {
			inGroupSet[nextNode] = 1;
			groups.push({'groupname':nextNode});
		}
		nextNode = level0[nextNode];		
	} while (nextNode != null && ! visited[nextNode]);

	// build the threads info. filter out floating threads
	var rs = get_relations_at_time(env, "this/SkipList<:owns", t);
	var threads = []
	rs.forEach(function (r) {
		var lst = r.split("->");
		if (inGroupSet[lst[2]]) {
			var obj = {'name': lst[1], 'groupname': lst[2]};
			threads.push(obj);
		}
	});
	return { 'groups' : groups, 
			 'links' : links, 
			 'nodes' : nodes,
			 'threads' : threads
		   };
}



