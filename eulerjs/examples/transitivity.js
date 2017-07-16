var cases = {
  "GND":{},
  "p":[
	{
	 head:{pred: "p", args:[{pred: ":A", args:[]}, {pred: ":B", args:[]}]}, 
	 body: []
	},
	{
	 head:{pred: "p", args:[{pred: ":B", args:[]}, {pred: ":C", args:[]}]}, 
	 body: []
	},
	{
	 head:{pred: "p", args:[{pred: ":C", args:[]}, {pred: ":D", args:[]}]}, 
	 body: []
	},

	{
	 head: { pred:"p", args:[{pred:"?x", args:[]}, {pred:"?z", args:[]}]}, 
	 body:[
	 {pred:"p", args:[{pred:"?x", args:[]}, {pred:"?y", args:[]}]},
	 {pred:"p", args:[{pred:"?y", args:[]}, {pred:"?z", args:[]}]}]
	} 
],
  "":[
    {head:{}, body:[{pred:"p", args:[{pred:":A", args:[]}, {pred:"?what", args:[]}]}]}
  ]
}

