# coding: utf-8
import json
import pprint
pp = pprint.PrettyPrinter(indent=2)
bg = json.load(open('chrome_bg_api.json','r'))
ct = json.load(open('chrome_api_OLD.json','r'))
#for key,val in ct.items():
	
#   if key not in bg:
#		bg[key]=val
	#	pp.pprint(val)

	

import collections # requires Python 2.7 -- see note below if you're using an earlier version
def merge_dict(d1, d2):
    """
    Modifies d1 in-place to contain values from d2.  If any value
    in d1 is a dictionary (or dict-like), *and* the corresponding
    value in d2 is also a dictionary, then merge them in-place.
    """
    for k,v2 in d2.items():
        v1 = d1.get(k) # returns None if v1 has no value for this key
        if ( isinstance(v1, collections.Mapping) and 
             isinstance(v2, collections.Mapping) ):
            merge_dict(v1, v2)
        else:
            d1[k] = v2
	
	
	
#final = {**ct, **bg}
merge_dict(bg, ct)

	
json.dump(bg, open('chrome_api.json','w+'), indent=2, sort_keys=True)
