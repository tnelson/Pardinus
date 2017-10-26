package kodkod.engine;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

import kodkod.ast.Relation;
import kodkod.instance.ElectrodProblemPrinter;
import kodkod.instance.Instance;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TemporalInstance;
import kodkod.instance.Tuple;
import kodkod.instance.TupleSet;

public class ElectrodProblemReader {
	
	private List<Instance> insts;
	private int loop = -1;
	private PardinusBounds bounds;
	
	public ElectrodProblemReader(PardinusBounds b) {
		insts = new ArrayList<Instance>();
		loop = -1;
		bounds = b;
	}
	
	public TemporalInstance read(File file) throws ParserConfigurationException, SAXException, IOException {
	    DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
	    factory.setValidating(false);
	    factory.setIgnoringElementContentWhitespace(true);
	    DocumentBuilder builder = factory.newDocumentBuilder();
	    Document doc = builder.parse(file);
	    Element root = doc.getDocumentElement();
	    NodeList elems = root.getChildNodes();
	    int c = 0;
	    for (int i = 0; i < elems.getLength(); i++) {
	    	if (elems.item(i).getNodeName().equals("st")) {
	    		if (elems.item(i).getAttributes().getNamedItem("loop-target").getNodeValue().equals("true"))
	    			loop = c;
	    		insts.add(state(elems.item(i)));
	    		c++;
	    	}
	    }
		
	    if (insts.size() == 0)
	    	return null;
		return new TemporalInstance(insts,loop);
	}
	
	private Instance state (Node node) {
		Instance inst = new Instance(bounds.universe());
		
		// TODO: how to handle integers in unbounded problems?
		
		for(Relation r : bounds.relations()) {
			NodeList e = null;
		    for (int i = 0; i < node.getChildNodes().getLength(); i++) {
		    	if (node.getChildNodes().item(i).getNodeName().equals("rel")) {
		    		String nm = ElectrodProblemPrinter.normRel(r.toString());
		    		if (node.getChildNodes().item(i).getAttributes().getNamedItem("name").getNodeValue().equals(nm))
		    			e = node.getChildNodes().item(i).getChildNodes();
		    	}
		    }
		    List<List<String>> buff__ = new ArrayList<List<String>>();

		    if (e != null)
			    for (int i = 0; i < e.getLength(); i++) {
			    	if (e.item(i).getNodeName().equals("t")) {
					    List<String> buff_ = new ArrayList<String>();
					    for (int j = 0; j < e.item(i).getChildNodes().getLength(); j++) {
					    	if (e.item(i).getChildNodes().item(j).getNodeName().equals("a")) {
					    		buff_.add(e.item(i).getChildNodes().item(j).getTextContent());
					    	}
					    }
					    buff__.add(buff_);
			    	}
			    }
		    
		    List<Tuple> buff = new ArrayList<Tuple>();
		    for (List<String> buff_: buff__) {
		    	List<Object> _buff = new ArrayList<Object>();
			    for (String x: buff_)
				    for (int i = 0; i < bounds.universe().size(); i++) {
				    	if (bounds.universe().atom(i).toString().equals(x))
				    		_buff.add(bounds.universe().atom(i));
				    }
			    buff.add(bounds.universe().factory().tuple(_buff));
		    }
		    
		    TupleSet t;
		    if (buff.isEmpty())
		    	t = bounds.universe().factory().noneOf(r.arity());
		    else t = bounds.universe().factory().setOf(buff);
		    
			inst.add(r, t);
		}
		
		return inst;
	}

}
